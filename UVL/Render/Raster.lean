import UVL.Render.FrameBuffer
import UVL.Render.RenderOp
import UVL.Render.Font

/-!
# CPU rasterizer

A pure-Lean software rasterizer for `RenderOp` scenes.

* Analytic shapes (rects, rounded rects, circles, ellipses, lines, shadows) are
  drawn from their signed distance field: one distance evaluation per pixel.
* Paths are flattened and filled with a scanline algorithm (exact horizontal
  coverage, 4 vertical sub-samples) under the non-zero or even-odd rule.
* Text uses the built-in bitmap font with exact area coverage.

All pixel loops run over a `Clip w h` whose bounds are proved `≤ w`/`≤ h`, so
pixel coordinates are produced as `Fin w`/`Fin h` with no bounds checks.
-/

namespace UVL.Raster

open FrameBuffer

/-- A pixel rectangle `[x0, x1) × [y0, y1)` proved to lie inside a `w × h` buffer. -/
structure Clip (w h : Nat) where
  x0 : Nat
  x1 : Nat
  y0 : Nat
  y1 : Nat
  hx : x1 ≤ w
  hy : y1 ≤ h

variable {w h : Nat}

def Clip.full (w h : Nat) : Clip w h := ⟨0, w, 0, h, Nat.le_refl _, Nat.le_refl _⟩

@[inline] def floatToNat (f : Float) : Nat := if f <= 0.0 then 0 else f.toUInt64.toNat

/-- Intersect a clip with a float rectangle given in device space (rounded
outwards). The buffer's pixel `(0, 0)` sits at device pixel `(ox, oy)`; the
rounding happens in device space and the shift is integer, so a tile sees
exactly the pixels the full frame would. -/
def Clip.inter (c : Clip w h) (r : Rect) (ox oy : Nat := 0) : Clip w h :=
  { x0 := Max.max c.x0 (floatToNat r.x.floor - ox)
    x1 := Min.min c.x1 (floatToNat (r.x + r.w).ceil - ox)
    y0 := Max.max c.y0 (floatToNat r.y.floor - oy)
    y1 := Min.min c.y1 (floatToNat (r.y + r.h).ceil - oy)
    hx := Nat.le_trans (Nat.min_le_left _ _) c.hx
    hy := Nat.le_trans (Nat.min_le_left _ _) c.hy }

def Clip.toRect (c : Clip w h) : Rect :=
  ⟨c.x0.toF, c.y0.toF, c.x1.toF - c.x0.toF, c.y1.toF - c.y0.toF⟩

/-- Rendering state: current transform (local → device), clip, and the device
position of the buffer's top-left pixel (non-zero when rendering a tile). -/
structure Ctx (w h : Nat) where
  m : Affine := {}
  clip : Clip w h
  ox : Nat := 0
  oy : Nat := 0

/-- Clip the context to a device-space rectangle. -/
@[inline] def Ctx.clipTo (ctx : Ctx w h) (r : Rect) : Clip w h := ctx.clip.inter r ctx.ox ctx.oy

/-- Device-space coordinate of the center of buffer column `x` / row `y`. -/
@[inline] def Ctx.cx (ctx : Ctx w h) (x : Nat) : Float := (x + ctx.ox).toF + 0.5
@[inline] def Ctx.cy (ctx : Ctx w h) (y : Nat) : Float := (y + ctx.oy).toF + 0.5

/-- Blend `paint` over every pixel of `bbox ∩ clip` with coverage `cov p`, where
`p` is the pixel center in device space. -/
@[inline] def fillCoverage (fb : FrameBuffer w h) (ctx : Ctx w h) (bbox : Rect)
    (paint : Paint) (cov : Vec2 → Float) : FrameBuffer w h :=
  let c := ctx.clipTo bbox
  let inv := ctx.m.inverse
  let solid := match paint with | .solid col => some col | _ => none
  foldRange c.y0 c.y1 c.hy fb fun fb y =>
    foldRange c.x0 c.x1 c.hx fb fun fb x =>
      let p : Vec2 := ⟨ctx.cx x.val, ctx.cy y.val⟩
      let a := cov p
      if a <= 0.0 then fb else
      let col := match solid with
        | some col => col
        | none => paint.colorAt (inv.apply p)
      fb.blend x y col a

/-- Local-space bounding box and signed distance of an analytic shape. -/
def sdfOf : Shape → Option (Rect × (Vec2 → Float))
  | .rect r => some (r, fun p => SDF.box p r.center r.halfSize)
  | .roundedRect r rad => some (r, fun p => SDF.roundedBox p r.center r.halfSize rad)
  | .circle c r => some (⟨c.x - r, c.y - r, 2 * r, 2 * r⟩, fun p => SDF.circle p c r)
  | .ellipse c rx ry => some (⟨c.x - rx, c.y - ry, 2 * rx, 2 * ry⟩, fun p => SDF.ellipse p c rx ry)
  | .line a b => some (Rect.ofPoints #[a, b], fun p => SDF.segment p a b)
  | .path .. => none

/-- Scan buffer row `y` from column `x` to `c.x1` (one row of `fillDistance`). -/
@[specialize] def scanRow (c : Clip w h) (ctx : Ctx w h) (y : Fin h) (outT inT lip blur : Float)
    (dist : Float → Float) (colorAt : Float → Color) (x : Nat) (fb : FrameBuffer w h) :
    FrameBuffer w h :=
  if hx : x < c.x1 then
    let px := ctx.cx x
    let d := dist px
    if d >= outT then
      -- skip every pixel that is provably outside
      scanRow c ctx y outT inT lip blur dist colorAt
        (x + Max.max 1 (floatToNat ((d - outT) / lip).floor)) fb
    else if d <= inT then
      -- fill every pixel that is provably fully covered
      let n := Max.max 1 (floatToNat ((inT - d) / lip).floor)
      let stop := Min.min c.x1 (x + n)
      let fb := foldRange x stop (Nat.le_trans (Nat.min_le_left _ _) c.hx) fb fun fb xi =>
        fb.blend xi y (colorAt (ctx.cx xi.val)) 1.0
      scanRow c ctx y outT inT lip blur dist colorAt stop fb
    else
      let fb := fb.blend ⟨x, Nat.lt_of_lt_of_le hx c.hx⟩ y (colorAt px)
        (SDF.blurredCoverage d blur)
      scanRow c ctx y outT inT lip blur dist colorAt (x + 1) fb
  else fb
termination_by c.x1 - x
decreasing_by all_goals omega

/-- Fill pixels of `clip ∩ bbox` from a *device-space* signed distance given
per row (`rowDist y` is the distance as a function of the pixel-centre `x`).

Distance fields are 1-Lipschitz, so one evaluation bounds a whole run of
pixels: far outside the shape we jump ahead `d` pixels at once, and deep
inside we fill a run of fully covered pixels without evaluating the field.
Only the anti-aliased boundary is evaluated pixel by pixel. For approximate
fields, `lip` bounds how fast the value can change per pixel. -/
@[specialize] def fillDistance (fb : FrameBuffer w h) (ctx : Ctx w h) (bbox : Rect) (paint : Paint)
    (rowDist : Float → Float → Float) (blur : Float := 0) (lip : Float := 1.0) :
    FrameBuffer w h :=
  let c := ctx.clipTo bbox
  let inv := ctx.m.inverse
  -- coverage is exactly 0 beyond `outT` and (numerically) 1 below `inT`
  let outT := if blur > 0 then 4.0 * blur + 0.5 else 0.5
  let inT := if blur > 0 then -4.0 * blur - 0.5 else -0.5
  match paint with
  | .solid col =>
    foldRange c.y0 c.y1 c.hy fb fun fb y =>
      let cy := ctx.cy y.val
      scanRow c ctx y outT inT lip blur (rowDist cy) (fun _ => col) c.x0 fb
  | _ =>
    foldRange c.y0 c.y1 c.hy fb fun fb y =>
      let cy := ctx.cy y.val
      scanRow c ctx y outT inT lip blur (rowDist cy) (fun px => paint.colorAt (inv.apply ⟨px, cy⟩))
        c.x0 fb

/-- Fill an SDF (given in local space) through the context transform. -/
@[inline] def fillSDF (fb : FrameBuffer w h) (ctx : Ctx w h) (bbox : Rect) (paint : Paint)
    (d : Vec2 → Float) (blur : Float := 0) (lip : Float := 1.0) : FrameBuffer w h :=
  let inv := ctx.m.inverse
  let s := ctx.m.scaleFactor
  let dev := (ctx.m.mapRect bbox).inflate (1.0 + 4.0 * blur)
  fillDistance fb ctx dev paint (fun cy px => d (inv.apply ⟨px, cy⟩) * s) blur lip

/-! ### Scanline path filling -/

structure Edge where
  x0 : Float
  y0 : Float
  x1 : Float
  y1 : Float
  dir : Int

def edgesOf (polys : Array Path.Poly) : Array Edge := Id.run do
  let mut es := #[]
  for poly in polys do
    let pts := poly.pts
    for i in [0:pts.size] do
      let a := pts[i]!
      let b := pts[(i + 1) % pts.size]!
      if a.y < b.y then es := es.push ⟨a.x, a.y, b.x, b.y, 1⟩
      else if a.y > b.y then es := es.push ⟨b.x, b.y, a.x, a.y, -1⟩
  return es

/-- Add a horizontal span `[xa, xb)` with weight `wt` to the row accumulator
(whose first cell is pixel column `xl`). -/
def addSpan (acc : Array Float) (xl : Nat) (xa xb wt : Float) : Array Float := Id.run do
  let lo := xl.toF
  let hi := lo + acc.size.toF
  let xa := if xa < lo then lo else if xa > hi then hi else xa
  let xb := if xb < lo then lo else if xb > hi then hi else xb
  if xb <= xa then return acc
  let ia := floatToNat xa.floor
  let ib := floatToNat xb.floor
  let mut acc := acc
  if ia == ib then
    acc := acc.modify (ia - xl) (· + (xb - xa) * wt)
  else
    acc := acc.modify (ia - xl) (· + ((ia + 1).toF - xa) * wt)
    for i in [ia + 1:ib] do
      acc := acc.modify (i - xl) (· + wt)
    acc := acc.modify (ib - xl) (· + (xb - ib.toF) * wt)
  return acc

def subSamples : Nat := 4

def fillPolys (fb : FrameBuffer w h) (ctx : Ctx w h) (polys : Array Path.Poly)
    (rule : FillRule) (paint : Paint) : FrameBuffer w h :=
  let edges := edgesOf polys
  if edges.isEmpty then fb else
  let bbox := Rect.ofPoints (polys.foldl (fun acc p => acc ++ p.pts) #[])
  let c := ctx.clipTo (bbox.inflate 1.0)
  let inv := ctx.m.inverse
  let width := c.x1 - c.x0
  foldRange c.y0 c.y1 c.hy fb fun fb y => Id.run do
    let rowTop := (y.val + ctx.oy).toF
    let rowEdges := edges.filter fun e => e.y1 > rowTop && e.y0 < rowTop + 1.0
    if rowEdges.isEmpty then return fb
    let mut acc : Array Float := Array.replicate width 0.0
    let wt := 1.0 / subSamples.toF
    for s in [0:subSamples] do
      let sy := rowTop + (s.toF + 0.5) / subSamples.toF
      let mut xs : Array (Float × Int) := #[]
      for e in rowEdges do
        if e.y0 <= sy && sy < e.y1 then
          xs := xs.push (e.x0 + (sy - e.y0) * (e.x1 - e.x0) / (e.y1 - e.y0), e.dir)
      let sorted := xs.qsort (fun a b => a.1 < b.1)
      let mut wind : Int := 0
      let mut start : Float := 0
      for (x, d) in sorted do
        let inside := if rule == .nonZero then wind != 0 else wind % 2 != 0
        wind := wind + d
        let inside' := if rule == .nonZero then wind != 0 else wind % 2 != 0
        if !inside && inside' then start := x
        else if inside && !inside' then acc := addSpan acc (c.x0 + ctx.ox) start x wt
    let solid := match paint with | .solid col => some col | _ => none
    return foldRange c.x0 c.x1 c.hx fb fun fb x =>
      let a := acc[x.val - c.x0]!
      if a <= 0.0 then fb else
      let col := match solid with
        | some col => col
        | none => paint.colorAt (inv.apply ⟨ctx.cx x.val, rowTop + 0.5⟩)
      fb.blend x y col (if a > 1.0 then 1.0 else a)

/-- Stroke polylines (device space) with round joins and caps. -/
def strokePolys (fb : FrameBuffer w h) (ctx : Ctx w h) (polys : Array Path.Poly)
    (width : Float) (paint : Paint) : FrameBuffer w h :=
  let hw := width * ctx.m.scaleFactor / 2.0
  let segs : Array (Vec2 × Vec2) := polys.foldl (init := #[]) fun acc poly =>
    let n := poly.pts.size
    let k := if poly.closed then n else n - 1
    (Array.range k).foldl (init := acc) fun acc i =>
      acc.push (poly.pts[i]!, poly.pts[(i + 1) % n]!)
  if segs.isEmpty then fb else
  let bbox := (Rect.ofPoints (polys.foldl (fun acc p => acc ++ p.pts) #[])).inflate (hw + 1.0)
  fillDistance fb ctx bbox paint fun cy =>
    let row := segs.filter fun (a, b) =>
      Min.min a.y b.y - hw - 1.0 <= cy && Max.max a.y b.y + hw + 1.0 >= cy
    fun px =>
      if row.isEmpty then 1.0e30 else
      let p : Vec2 := ⟨px, cy⟩
      row.foldl (fun d (a, b) => Min.min d (SDF.segment p a b)) 1.0e30 - hw

/-! ### Text -/

@[inline] def overlap (a0 a1 b0 b1 : Float) : Float :=
  let lo := Max.max a0 b0
  let hi := Min.min a1 b1
  if hi > lo then hi - lo else 0.0

def drawText (fb : FrameBuffer w h) (ctx : Ctx w h) (pos : Vec2) (s : String)
    (scale : Float) (color : Color) : FrameBuffer w h :=
  let o := ctx.m.apply pos
  let sc := scale * ctx.m.scaleFactor
  let chars := s.toList.toArray
  (Array.range chars.size).foldl (init := fb) fun fb k =>
    let g := Font.glyph chars[k]!
    let gx := o.x + (k * Font.advance).toF * sc
    let c := ctx.clipTo ⟨gx, o.y, 5.0 * sc, 7.0 * sc⟩
    -- per pixel row: vertical overlap with each glyph row (separable box filter)
    let oys := fun (py : Float) => (Array.range 7).map fun j =>
      overlap py (py + 1.0) (o.y + j.toF * sc) (o.y + (j + 1).toF * sc)
    -- per pixel column: horizontal coverage of each glyph row's bits
    let rowCov := fun (px : Float) => (Array.range 7).map fun j =>
      let bits := g[j]!
      (Array.range 5).foldl (init := 0.0) fun acc i =>
        if (bits >>> (4 - i)) % 2 == 1 then
          acc + overlap px (px + 1.0) (gx + i.toF * sc) (gx + (i + 1).toF * sc)
        else acc
    let cols := (Array.range (c.x1 - c.x0)).map fun i => rowCov (c.x0 + i + ctx.ox).toF
    foldRange c.y0 c.y1 c.hy fb fun fb y =>
      let oy := oys (y.val + ctx.oy).toF
      foldRange c.x0 c.x1 c.hx fb fun fb x =>
        let rc := cols[x.val - c.x0]!
        let cov := (oy.zipWith (· * ·) rc).foldl (· + ·) 0.0
        if cov <= 0.0 then fb else fb.blend x y color (if cov > 1.0 then 1.0 else cov)

/-! ### Dispatch -/

@[inline] def strokeSDF (fb : FrameBuffer w h) (ctx : Ctx w h) (bbox : Rect) (width : Float)
    (paint : Paint) (d : Vec2 → Float) (lip : Float := 1.0) : FrameBuffer w h :=
  fillSDF fb ctx (bbox.inflate (width / 2.0)) paint (fun p => (d p).abs - width / 2.0) 0 lip

/-- Bound on how fast a shape's field changes per pixel (1 for exact SDFs). -/
def lipOf : Shape → Float
  | .ellipse _ rx ry => 2.0 * Max.max rx ry / Max.max (Min.min rx ry) 1.0e-6
  | _ => 1.0

/-! Shapes are dispatched with a literal distance function per case (rather than
through `sdfOf`), so the compiler specializes the whole scan loop for each
shape kind: no closures or boxed floats per pixel. -/

def fillShape (ctx : Ctx w h) (fb : FrameBuffer w h) (s : Shape) (paint : Paint) :
    FrameBuffer w h :=
  match s with
  | .rect r =>
    let c := r.center; let hs := r.halfSize
    fillSDF fb ctx r paint (fun p => SDF.box p c hs)
  | .roundedRect r rad =>
    let c := r.center; let hs := r.halfSize
    fillSDF fb ctx r paint (fun p => SDF.roundedBox p c hs rad)
  | .circle c r => fillSDF fb ctx ⟨c.x - r, c.y - r, 2 * r, 2 * r⟩ paint (fun p => SDF.circle p c r)
  | .ellipse c rx ry =>
    fillSDF fb ctx ⟨c.x - rx, c.y - ry, 2 * rx, 2 * ry⟩ paint (fun p => SDF.ellipse p c rx ry) 0
      (lipOf s)
  | .line a b => fillSDF fb ctx (Rect.ofPoints #[a, b]) paint (fun p => SDF.segment p a b)
  | .path .. => fb

def strokeShape (ctx : Ctx w h) (fb : FrameBuffer w h) (s : Shape) (width : Float)
    (paint : Paint) : FrameBuffer w h :=
  match s with
  | .rect r =>
    let c := r.center; let hs := r.halfSize
    strokeSDF fb ctx r width paint (fun p => SDF.box p c hs)
  | .roundedRect r rad =>
    let c := r.center; let hs := r.halfSize
    strokeSDF fb ctx r width paint (fun p => SDF.roundedBox p c hs rad)
  | .circle c r =>
    strokeSDF fb ctx ⟨c.x - r, c.y - r, 2 * r, 2 * r⟩ width paint (fun p => SDF.circle p c r)
  | .ellipse c rx ry =>
    strokeSDF fb ctx ⟨c.x - rx, c.y - ry, 2 * rx, 2 * ry⟩ width paint
      (fun p => SDF.ellipse p c rx ry) (lipOf s)
  | .line a b =>
    fillSDF fb ctx ((Rect.ofPoints #[a, b]).inflate (width / 2.0)) paint
      fun p => SDF.segment p a b - width / 2.0
  | .path .. => fb

partial def renderOp (ctx : Ctx w h) (fb : FrameBuffer w h) : RenderOp → FrameBuffer w h
  | .fill (.path p rule) paint => fillPolys fb ctx (p.flatten ctx.m) rule paint
  | .fill s paint => fillShape ctx fb s paint
  | .stroke (.path p _) width paint => strokePolys fb ctx (p.flatten ctx.m) width paint
  | .stroke s width paint => strokeShape ctx fb s width paint
  | .shadow r radius blur c =>
    let rc := r.center; let hs := r.halfSize
    fillSDF fb ctx r (.solid c) (fun p => SDF.roundedBox p rc hs (.all radius))
      (blur * ctx.m.scaleFactor)
  | .text pos s scale c => drawText fb ctx pos s scale c
  | .transform m ops => ops.foldl (renderOp { ctx with m := ctx.m.compose m }) fb
  | .clip r ops => ops.foldl (renderOp { ctx with clip := ctx.clipTo (ctx.m.mapRect r) }) fb
  | .group ops => ops.foldl (renderOp ctx) fb

/-- Render a scene onto an existing buffer. -/
def renderInto (fb : FrameBuffer w h) (ops : Array RenderOp) : FrameBuffer w h :=
  ops.foldl (renderOp { clip := Clip.full w h }) fb

/-- Render a scene onto a fresh `w × h` buffer cleared to `bg`. -/
def render (w h : Nat) (ops : Array RenderOp) (bg : Color := Color.white) : FrameBuffer w h :=
  renderInto (FrameBuffer.new w h bg) ops

/-- Render only the `tw × th` window of the scene whose top-left device pixel is
`(ox, oy)`. Every pixel gets exactly the value it has in `render` (same device
coordinates, same blend sequence); see `Render/Tile.lean`. -/
def renderWindow (ox oy tw th : Nat) (ops : Array RenderOp) (bg : Color := Color.white) :
    FrameBuffer tw th :=
  ops.foldl (renderOp { clip := Clip.full tw th, ox, oy }) (FrameBuffer.new tw th bg)

end UVL.Raster
