import UVL.Render.Path

/-!
# Multi-channel signed distance fields (MSDF)

A glyph atlas for drawing a lot of text quickly. Each glyph outline is turned,
once, into a small grid (`cellSize²` texels) of three signed distances, one per
color channel (Chlumsky's MSDF). Drawing a glyph then costs a bilinear lookup
and a median per pixel, independent of the outline's complexity, at any size,
rotation or scale; corners stay sharp because each channel only measures the
distance to the edges of its color.

Generation, in pure Lean:

1. The outline is split into contours of line and quadratic edges.
2. Edges are colored: at every corner (sharp turn of the tangent) the color
   changes, so the two edges meeting at a corner never share all channels.
3. For every texel and channel, the edge of that channel nearest to the texel
   center gives a signed *pseudo*-distance (distance to the edge, extended
   along its tangent past its ends).
4. Texels where the median of the three channels has the wrong inside/outside
   sign (decided exactly, by winding number) fall back to the true signed
   distance in all channels.

Distances are stored in ems as `Float`s, positive inside. `sample` is the one
lookup both renderers use: the CPU rasterizer calls it directly and the GPU
kernel (`GPU/Kernels.lean`) performs the same operations in the same order.

Atlas texels are computed lazily, glyph by glyph (`Thunk`), the first time a
glyph is drawn.
-/

namespace UVL.MSDF

/-- Texels per side of a glyph cell. -/
def cellSize : Nat := 32

/-- Floats per glyph cell (three channels per texel). -/
def cellFloats : Nat := cellSize * cellSize * 3

/-- Margin around a glyph's outline in its cell, in ems. It must exceed half a
pixel at the smallest size drawn (0.125 em: down to 4 px). -/
def padding : Float := 0.125

/-- Placement of a glyph cell in em space (y down): the center of texel `(i, j)`
is at `(x + (i + 0.5) * texel, y + (j + 0.5) * texel)`; the glyph's outline plus
padding covers `w × h` ems from `(x, y)`. -/
structure Cell where
  x : Float := 0
  y : Float := 0
  texel : Float := 1
  w : Float := 0
  h : Float := 0
deriving Inhabited, Repr, BEq

/-- An atlas: one cell per glyph and its lazily computed texels. Atlases are
compared by `id` (two atlases with the same id must hold the same glyphs). -/
structure Atlas where
  id : Nat
  cells : Array Cell
  texels : Array (Thunk FloatArray)

instance : Inhabited Atlas := ⟨{ id := 0, cells := #[], texels := #[] }⟩
instance : BEq Atlas := ⟨fun a b => a.id == b.id⟩

/-- A glyph to draw: atlas glyph index, pen position on the baseline (local
coordinates) and size in pixels per em. -/
structure GlyphQuad where
  glyph : Nat
  x : Float
  y : Float
  size : Float
deriving Inhabited, Repr, BEq

namespace Atlas

def cell (a : Atlas) (g : Nat) : Cell := a.cells[g]?.getD {}

def glyphTexels (a : Atlas) (g : Nat) : FloatArray :=
  match a.texels[g]? with
  | some t => t.get
  | none => .empty

/-- Local-space rectangle covered by a glyph quad. -/
def quadRect (a : Atlas) (q : GlyphQuad) : Rect :=
  let c := a.cell q.glyph
  ⟨q.x + c.x * q.size, q.y + c.y * q.size, c.w * q.size, c.h * q.size⟩

end Atlas

/-! ### Sampling -/

@[inline] def median (r g b : Float) : Float := Max.max (Min.min r g) (Min.min (Max.max r g) b)

/-- Signed distance (ems, positive inside) at texel coordinates `(tx, ty)` of a
cell whose texels start at `tex[off]` (texel centres at integers, clamped to the
edge): bilinear interpolation of each channel, then the median. -/
def sampleTexel (tex : FloatArray) (off : Nat) (tx ty : Float) : Float :=
  let last := (cellSize - 1).toF
  let fx := tx.floor
  let fy := ty.floor
  let ax := tx - fx
  let ay := ty - fy
  -- written out (no local functions) so the compiled loop does not allocate
  let x0 := (Min.min (Max.max fx 0) last).toUSize
  let x1 := (Min.min (Max.max (fx + 1) 0) last).toUSize
  let y0 := (Min.min (Max.max fy 0) last).toUSize
  let y1 := (Min.min (Max.max (fy + 1) 0) last).toUSize
  let o := off.toUSize
  let row := cellSize.toUSize
  let i00 := o + (y0 * row + x0) * 3
  let i10 := o + (y0 * row + x1) * 3
  let i01 := o + (y1 * row + x0) * 3
  let i11 := o + (y1 * row + x1) * 3
  let r := lerp2 (tex.get! i00.toNat) (tex.get! i10.toNat) (tex.get! i01.toNat) (tex.get! i11.toNat) ax ay
  let g := lerp2 (tex.get! (i00 + 1).toNat) (tex.get! (i10 + 1).toNat) (tex.get! (i01 + 1).toNat)
    (tex.get! (i11 + 1).toNat) ax ay
  let b := lerp2 (tex.get! (i00 + 2).toNat) (tex.get! (i10 + 2).toNat) (tex.get! (i01 + 2).toNat)
    (tex.get! (i11 + 2).toNat) ax ay
  median r g b
where
  @[inline] lerp2 (v00 v10 v01 v11 ax ay : Float) : Float :=
    let top := v00 + ax * (v10 - v00)
    let bot := v01 + ax * (v11 - v01)
    top + ay * (bot - top)

/-- Signed distance (ems, positive inside) at em point `(u, v)` of cell `c`
whose texels start at `tex[off]`: bilinear interpolation of each channel, then
the median. -/
@[inline] def sample (tex : FloatArray) (off : Nat) (c : Cell) (u v : Float) : Float :=
  sampleTexel tex off ((u - c.x) / c.texel - 0.5) ((v - c.y) / c.texel - 0.5)

/-- Coverage of a pixel from the sampled distance: `d` ems at `pxPerEm` pixels
per em, through a one-pixel ramp. -/
@[inline] def coverage (d pxPerEm : Float) : Float :=
  Min.min (Max.max (d * pxPerEm + 0.5) 0) 1

/-! ### Generation -/

/-- An outline edge. -/
inductive Edge where
  | line (a b : Vec2)
  | quad (a c b : Vec2)
deriving Inhabited

namespace Edge

def startDir : Edge → Vec2
  | .line a b => b - a
  | .quad a c b => if c.x == a.x && c.y == a.y then b - a else c - a

def endDir : Edge → Vec2
  | .line a b => b - a
  | .quad a c b => if c.x == b.x && c.y == b.y then b - a else b - c

end Edge

/-- Contours of a path as closed loops of edges (cubics are split into
quadratics through their flattening points; fonts used here have none). -/
def contours (p : Path) : Array (Array Edge) := Id.run do
  let mut out : Array (Array Edge) := #[]
  let mut cur : Array Edge := #[]
  let mut start : Vec2 := ⟨0, 0⟩
  let mut pen : Vec2 := ⟨0, 0⟩
  let finish (cur : Array Edge) (pen start : Vec2) : Array Edge :=
    if cur.isEmpty then cur
    else if pen.x == start.x && pen.y == start.y then cur
    else cur.push (.line pen start)
  for c in p.cmds do
    match c with
    | .moveTo q =>
      let e := finish cur pen start
      if !e.isEmpty then out := out.push e
      cur := #[]; start := q; pen := q
    | .lineTo q =>
      if !(q.x == pen.x && q.y == pen.y) then cur := cur.push (.line pen q)
      pen := q
    | .quadTo c q => cur := cur.push (.quad pen c q); pen := q
    | .cubicTo c1 c2 q =>
      -- approximate by two quadratics (adequate for the rare cubic outline)
      let m : Vec2 := ⟨(pen.x + 3 * (c1.x + c2.x) + q.x) / 8, (pen.y + 3 * (c1.y + c2.y) + q.y) / 8⟩
      let qa : Vec2 := ⟨(pen.x + 3 * c1.x) / 4, (pen.y + 3 * c1.y) / 4⟩
      let qb : Vec2 := ⟨(3 * c2.x + q.x) / 4, (3 * c2.y + q.y) / 4⟩
      cur := cur.push (.quad pen qa m) |>.push (.quad m qb q)
      pen := q
    | .close =>
      let e := finish cur pen start
      if !e.isEmpty then out := out.push e
      cur := #[]; pen := start
  let e := finish cur pen start
  if !e.isEmpty then out := out.push e
  return out

/-- Membership in an array of naturals. (Written out: the compiled
specialization of `Array.contains` lives in the `Lean` package, which the
WebAssembly build does not link.) -/
def hasNat (a : Array Nat) (n : Nat) : Bool := a.any (· == n)

/-- Channel masks: red 1, green 2, blue 4. -/
def white : Nat := 7
def cyan : Nat := 6
def magenta : Nat := 5
def yellow : Nat := 3

private def norm (v : Vec2) : Vec2 :=
  let l := Float.sqrt (v.x * v.x + v.y * v.y)
  if l == 0 then v else ⟨v.x / l, v.y / l⟩

/-- A sharp turn between two tangent directions (msdfgen's criterion with an
angle threshold of 3 radians). -/
def isCorner (a b : Vec2) : Bool :=
  let a := norm a; let b := norm b
  a.x * b.x + a.y * b.y <= 0 || (a.x * b.y - a.y * b.x).abs > 0.14112000806

/-- Edge colors of one contour (msdfgen's "simple" coloring). -/
def colorContour (es : Array Edge) : Array Nat := Id.run do
  let n := es.size
  let mut corners : Array Nat := #[]
  for i in [0:n] do
    if isCorner (es[(i + n - 1) % n]!.endDir) (es[i]!.startDir) then corners := corners.push i
  let mut colors := Array.replicate n white
  if corners.size == 1 then
    -- a teardrop: three color groups around the single corner
    if n ≥ 3 then
      let s := corners[0]!
      for k in [0:n] do
        colors := colors.set! ((s + k) % n) #[magenta, white, yellow][3 * k / n]!
    else if n == 2 then
      colors := #[magenta, yellow]
  else if corners.size > 1 then
    let s := corners[0]!
    let mut color := cyan
    let mut seen := 0
    for k in [0:n] do
      let e := (s + k) % n
      if k > 0 && hasNat corners e then
        seen := seen + 1
        let next := if color == cyan then magenta else if color == magenta then yellow else cyan
        -- the last spline must differ from the first one too
        color := if seen == corners.size - 1 && next == cyan then
          (if color == magenta then yellow else magenta) else next
      colors := colors.set! e color
  return colors

/-- A straight piece of a flattened edge, with its channel mask and whether its
pseudo-distance extends past each end (only at the ends of the original edge). -/
structure Seg where
  a : Vec2
  b : Vec2
  mask : Nat
  extA : Bool
  extB : Bool

/-- Pieces per quadratic edge. -/
def quadPieces : Nat := 8

def segments (p : Path) : Array Seg := Id.run do
  let mut out : Array Seg := #[]
  for cs in contours p do
    let colors := colorContour cs
    for i in [0:cs.size] do
      let mask := colors[i]!
      match cs[i]! with
      | .line a b => out := out.push { a, b, mask, extA := true, extB := true }
      | .quad a c b =>
        let at_ (t : Float) : Vec2 :=
          let u := 1 - t
          ⟨u * u * a.x + 2 * u * t * c.x + t * t * b.x, u * u * a.y + 2 * u * t * c.y + t * t * b.y⟩
        for k in [0:quadPieces] do
          out := out.push { a := at_ (k.toF / quadPieces.toF), b := at_ ((k + 1).toF / quadPieces.toF),
                            mask, extA := k == 0, extB := k + 1 == quadPieces }
  return out

/-- Nearest-edge candidate: unsigned distance, end-point obliqueness (smaller
wins ties) and signed pseudo-distance. -/
structure Near where
  dist : Float := 1.0e30
  dot : Float := 1
  pseudo : Float := -1.0e30

@[inline] def Near.better (n : Near) (dist dot : Float) : Bool :=
  dist < n.dist - 1.0e-12 || (dist <= n.dist + 1.0e-12 && dot < n.dot)

/-- Running result of the nearest-edge search for one texel: the nearest
candidate per channel and overall, and the winding number. -/
structure Search where
  r : Near := {}
  g : Near := {}
  b : Near := {}
  all : Near := {}
  wind : Int := 0
deriving Inhabited

/-- Segment `k` of a flat segment table (`segStride` floats each:
`ax ay bx by mask extA extB`). -/
def segStride : Nat := 7

/-- The nearest-edge search for the texel centre `(px, py)` over segments
`k..n` of the flat table `t`. A loop with scalar arguments, so that it runs
without allocating except when a candidate improves. -/
def search (t : FloatArray) (n : Nat) (px py : Float) (k : Nat) (acc : Search) : Search :=
  if k < n then
    let o := k * segStride
    let ax := t.get! o; let ay := t.get! (o + 1)
    let bx := t.get! (o + 2); let by_ := t.get! (o + 3)
    let mask := (t.get! (o + 4)).toUInt8
    let extA := t.get! (o + 5) > 0
    let extB := t.get! (o + 6) > 0
    let abx := bx - ax
    let aby := by_ - ay
    let apx := px - ax
    let apy := py - ay
    let l2 := abx * abx + aby * aby
    let tt := (apx * abx + apy * aby) / l2
    let tc := Min.min (Max.max tt 0) 1
    let dx := apx - tc * abx
    let dy := apy - tc * aby
    let d2 := dx * dx + dy * dy
    -- winding number of a horizontal ray to the right
    let wind :=
      if (ay <= py && py < by_) || (by_ <= py && py < ay) then
        let xc := ax + (py - ay) * abx / aby
        if xc > px then acc.wind + (if by_ > ay then 1 else -1) else acc.wind
      else acc.wind
    -- farther than every candidate this segment could replace: only the
    -- winding number can change (the bound is padded, so results are exact)
    let bound := Max.max acc.all.dist <| Max.max (if mask % 2 == 1 then acc.r.dist else 0) <|
      Max.max (if mask / 2 % 2 == 1 then acc.g.dist else 0) (if mask / 4 % 2 == 1 then acc.b.dist else 0)
    let bound := bound * 1.000001 + 1.0e-9
    if bound < 1.0e29 && d2 > bound * bound then
      search t n px py (k + 1) { acc with wind }
    else
    let dist := Float.sqrt d2
    let cross := abx * apy - aby * apx
    let len := Float.sqrt l2
    let sgn := if cross < 0 then -1.0 else 1.0
    let dot := if (tt < 0 || tt > 1) && dist > 0 then
      ((abx * dx + aby * dy) / (len * dist)).abs else 0
    let pseudo := if (tt < 0 && extA) || (tt > 1 && extB) then cross / len else sgn * dist
    let acc := if acc.all.better dist dot || wind != acc.wind ||
        (mask % 2 == 1 && acc.r.better dist dot) || (mask / 2 % 2 == 1 && acc.g.better dist dot) ||
        (mask / 4 % 2 == 1 && acc.b.better dist dot) then
      { all := if acc.all.better dist dot then { dist, dot, pseudo := sgn * dist } else acc.all
        r := if mask % 2 == 1 && acc.r.better dist dot then { dist, dot, pseudo } else acc.r
        g := if mask / 2 % 2 == 1 && acc.g.better dist dot then { dist, dot, pseudo } else acc.g
        b := if mask / 4 % 2 == 1 && acc.b.better dist dot then { dist, dot, pseudo } else acc.b
        wind }
      else acc
    search t n px py (k + 1) acc
  else acc
termination_by n - k

/-- Texels of one glyph cell for the outline `p` (ems, y down). -/
def generate (p : Path) (c : Cell) : FloatArray := Id.run do
  let segs := (segments p).filter fun s => s.a.x != s.b.x || s.a.y != s.b.y
  let mut out := FloatArray.emptyWithCapacity cellFloats
  if segs.isEmpty then
    for _ in [0:cellFloats] do out := out.push (-1.0)
    return out
  let table := segs.foldl (init := FloatArray.emptyWithCapacity (segs.size * segStride)) fun t s =>
    t.push s.a.x |>.push s.a.y |>.push s.b.x |>.push s.b.y |>.push s.mask.toFloat
      |>.push (if s.extA then 1 else 0) |>.push (if s.extB then 1 else 0)
  -- texel values before the sign is fixed, and whether each texel is inside
  let mut raw : Array (Float × Float × Float × Float) := #[]
  let mut agree : Int := 0
  for j in [0:cellSize] do
    for i in [0:cellSize] do
      let px := c.x + (i.toF + 0.5) * c.texel
      let py := c.y + (j.toF + 0.5) * c.texel
      let res := search table segs.size px py 0 {}
      let all := res.all
      let inside := res.wind != 0
      let sd := if inside then all.dist else -all.dist
      -- does the edge orientation say "inside" where the winding number does?
      if all.dist > 1.0e-9 then
        agree := agree + (if (all.pseudo > 0) == inside then 1 else -1)
      raw := raw.push (res.r.pseudo, res.g.pseudo, res.b.pseudo, sd)
  -- contour orientation decides the sign of the pseudo-distances; flip them
  -- so that inside is positive
  let flip := if agree < 0 then -1.0 else 1.0
  for (r, g, b, sd) in raw do
    let r := r * flip; let g := g * flip; let b := b * flip
    let m := median r g b
    if (m > 0) != (sd > 0) || m == 0 then
      out := out.push sd |>.push sd |>.push sd
    else
      out := out.push r |>.push g |>.push b
  return out

/-- The cell of an outline: its control-point bounding box plus `padding`,
with square texels fitting the longer side. -/
def cellOf (p : Path) : Cell :=
  let pts := p.controlPoints
  if pts.isEmpty then {} else
  let bb := Rect.ofPoints pts
  let w := bb.w + 2 * padding
  let h := bb.h + 2 * padding
  { x := bb.x - padding, y := bb.y - padding, texel := Max.max w h / cellSize.toF, w, h }

/-- An atlas for the given glyph outlines (ems, y down); texels are computed on
first use. -/
def Atlas.ofOutlines (id : Nat) (outlines : Array Path) : Atlas :=
  let cells := outlines.map cellOf
  { id, cells,
    texels := (Array.range outlines.size).map fun g =>
      Thunk.mk fun _ => generate outlines[g]! cells[g]! }

end UVL.MSDF
