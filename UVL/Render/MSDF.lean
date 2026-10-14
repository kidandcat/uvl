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

/-- Signed distance (ems, positive inside) at em point `(u, v)` of cell `c`
whose texels start at `tex[off]`: bilinear interpolation of each channel, then
the median. -/
def sample (tex : FloatArray) (off : Nat) (c : Cell) (u v : Float) : Float :=
  let last := (cellSize - 1).toF
  let tx := (u - c.x) / c.texel - 0.5
  let ty := (v - c.y) / c.texel - 0.5
  let fx := tx.floor
  let fy := ty.floor
  let ax := tx - fx
  let ay := ty - fy
  let x0 := (Min.min (Max.max fx 0) last).toUInt32.toNat
  let x1 := (Min.min (Max.max (fx + 1) 0) last).toUInt32.toNat
  let y0 := (Min.min (Max.max fy 0) last).toUInt32.toNat
  let y1 := (Min.min (Max.max (fy + 1) 0) last).toUInt32.toNat
  let at_ (x y k : Nat) : Float := tex[off + (y * cellSize + x) * 3 + k]!
  let chan (k : Nat) : Float :=
    let v00 := at_ x0 y0 k
    let v10 := at_ x1 y0 k
    let v01 := at_ x0 y1 k
    let v11 := at_ x1 y1 k
    let top := v00 + ax * (v10 - v00)
    let bot := v01 + ax * (v11 - v01)
    top + ay * (bot - top)
  median (chan 0) (chan 1) (chan 2)

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

/-- Texels of one glyph cell for the outline `p` (ems, y down). -/
def generate (p : Path) (c : Cell) : FloatArray := Id.run do
  let segs := (segments p).filter fun s => s.a.x != s.b.x || s.a.y != s.b.y
  let mut out := FloatArray.emptyWithCapacity cellFloats
  if segs.isEmpty then
    for _ in [0:cellFloats] do out := out.push (-1.0)
    return out
  -- texel values before the sign is fixed, and whether each texel is inside
  let mut raw : Array (Float × Float × Float × Float) := #[]
  let mut agree : Int := 0
  for j in [0:cellSize] do
    for i in [0:cellSize] do
      let px := c.x + (i.toF + 0.5) * c.texel
      let py := c.y + (j.toF + 0.5) * c.texel
      let mut r : Near := {}
      let mut g : Near := {}
      let mut b : Near := {}
      let mut all : Near := {}
      let mut wind : Int := 0
      for s in segs do
        let abx := s.b.x - s.a.x
        let aby := s.b.y - s.a.y
        let apx := px - s.a.x
        let apy := py - s.a.y
        let l2 := abx * abx + aby * aby
        let t := (apx * abx + apy * aby) / l2
        let tc := Min.min (Max.max t 0) 1
        let dx := apx - tc * abx
        let dy := apy - tc * aby
        let dist := Float.sqrt (dx * dx + dy * dy)
        let cross := abx * apy - aby * apx
        let len := Float.sqrt l2
        let sgn := if cross < 0 then -1.0 else 1.0
        let dot := if (t < 0 || t > 1) && dist > 0 then
          ((abx * dx + aby * dy) / (len * dist)).abs else 0
        let pseudo := if (t < 0 && s.extA) || (t > 1 && s.extB) then cross / len else sgn * dist
        -- winding number of a horizontal ray to the right
        if (s.a.y <= py && py < s.b.y) || (s.b.y <= py && py < s.a.y) then
          let xc := s.a.x + (py - s.a.y) * abx / aby
          if xc > px then wind := wind + (if s.b.y > s.a.y then 1 else -1)
        if all.better dist dot then all := { dist, dot, pseudo := sgn * dist }
        if s.mask % 2 == 1 && r.better dist dot then r := { dist, dot, pseudo }
        if s.mask / 2 % 2 == 1 && g.better dist dot then g := { dist, dot, pseudo }
        if s.mask / 4 % 2 == 1 && b.better dist dot then b := { dist, dot, pseudo }
      let inside := wind != 0
      let sd := if inside then all.dist else -all.dist
      -- does the edge orientation say "inside" where the winding number does?
      if all.dist > 1.0e-9 then
        agree := agree + (if (all.pseudo > 0) == inside then 1 else -1)
      raw := raw.push (r.pseudo, g.pseudo, b.pseudo, sd)
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
