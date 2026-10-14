import UVL.GPU.WGSL

/-!
# GPU kernels

The fragment program of the GPU renderer, written in the typed DSL of
`GPU/WGSL.lean`. Each render op is lowered (`GPU/Batch.lean`) to one or more
*primitives*: a screen-aligned pixel rectangle (two triangles) plus the
parameters needed to compute, for every pixel it covers, the same coverage and
color as the CPU rasterizer (`Render/Raster.lean`):

* analytic shapes and shadows: the signed distance field, evaluated in the
  shader (the same formulas as `Render/SDF.lean`);
* filled paths: the scanline rule of `Raster.fillPolys` evaluated per pixel
  (4 sub-scanlines, exact horizontal coverage) over the path's edges;
* stroked paths: distance to the flattened polyline;
* text: exact area coverage of the bitmap glyph cells.

Blending is the fixed-function `src-alpha, one-minus-src-alpha`, which is what
`FrameBuffer.blend` computes over an opaque background.
-/

namespace UVL.GPU

open Expr

/-- Floats per primitive record in the `prims` buffer. -/
def primStride : Nat := 36

/-- Primitive kinds (slot 0 of a record). -/
def kindShape : Nat := 0
def kindShadow : Nat := 1
def kindPathFill : Nat := 2
def kindPathStroke : Nat := 3
def kindGlyph : Nat := 4

def prims : Buffer := ⟨"prims"⟩
def data : Buffer := ⟨"data"⟩

def litN (n : Nat) : Expr .f32 := .litF n.toF

/-! ### Signed distance functions (`Render/SDF.lean`) -/

def sdCircleDef := Fn.def3 "sd_circle" .v2 .v2 .f32 .f32 fun p c r => do
  ret (length (p - c) - r)

def sdRoundedBoxDef := Fn.def4 "sd_rounded_box" .v2 .v2 .v2 .v4 .f32 fun p c b rad => do
  let q ← let_ (p - c)
  let r ← let_ (select (x q >. 0) (select (y q >. 0) (comp rad 2) (comp rad 1))
    (select (y q >. 0) (comp rad 3) (comp rad 0)))
  let r ← let_ (Expr.min r (Expr.min (x b) (y b)))
  let d ← let_ (vec2 (abs (x q) - x b + r) (abs (y q) - y b + r))
  ret (Expr.min (Expr.max (x d) (y d)) 0 + length (Expr.max d (vec2 0 0)) - r)

def sdSegmentDef := Fn.def3 "sd_segment" .v2 .v2 .v2 .f32 fun p a b => do
  let pa ← let_ (p - a)
  let ba ← let_ (b - a)
  let l2 ← let_ (dot ba ba)
  let t ← let_ (select (l2 ==. 0) 0 (clamp (dot pa ba / l2) 0 1))
  ret (length (pa - t * ba))

def sdEllipseDef := Fn.def4 "sd_ellipse" .v2 .v2 .f32 .f32 .f32 fun p c rx ry => do
  let q ← let_ (p - c)
  let k0 ← let_ (length (vec2 (x q / rx) (y q / ry)))
  let k1 ← let_ (length (vec2 (x q / (rx * rx)) (y q / (ry * ry))))
  if_ (k1 ==. 0) (ret (-(Expr.min rx ry)))
  ret (k0 * (k0 - 1) / k1)

/-- Abramowitz–Stegun `erf`, as `SDF.erf`. -/
def erfDef := Fn.def1 "erf_as" .f32 .f32 fun v => do
  let s ← let_ (select (v <. 0) (-1) 1)
  let a ← let_ (abs v)
  let t ← let_ (1 / (1 + 0.3275911 * a))
  let yv ← let_ (1 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t
    - 0.284496736) * t + 0.254829592) * t * exp (-a * a))
  ret (s * yv)

def sdCircle := sdCircleDef.2
def sdRoundedBox := sdRoundedBoxDef.2
def sdSegment := sdSegmentDef.2
def sdEllipse := sdEllipseDef.2
def erf := erfDef.2

/-- `SDF.coverage`: 1px box filter from the distance at the pixel center. -/
def coverage (d : Expr .f32) : Expr .f32 := clamp (0.5 - d) 0 1

def overlapDef := Fn.def4 "overlap" .f32 .f32 .f32 .f32 .f32 fun a0 a1 b0 b1 => do
  let lo ← let_ (Expr.max a0 b0)
  let hi ← let_ (Expr.min a1 b1)
  ret (select (hi >. lo) (hi - lo) 0)

def overlap := overlapDef.2

/-! ### Paint (`Render/Paint.lean`) -/

def rgba (base : Expr .u32) : Expr .v4 :=
  vec4 (load data base) (load data (base + 1)) (load data (base + 2)) (load data (base + 3))

def mix4 (a b : Expr .v4) (t : Expr .f32) : Expr .v4 :=
  a + vec4 t t t t * (b - a)

/-- `Paint.sampleStops` over `n` stops at `data[off..]` (5 floats each). -/
def sampleStopsDef := Fn.def3 "sample_stops" .f32 .f32 .f32 .v4 fun off n t0 => do
  if_ (n <. 1) (ret (vec4 0 0 0 0))
  let t ← let_ (clamp t0 0 1)
  let o ← let_ (toU off)
  let firstOff ← let_ (load data o)
  let firstCol ← let_ (rgba (o + 1))
  if_ (t <=. firstOff) (ret firstCol)
  let prevOff ← var_ firstOff
  let prevCol ← var_ firstCol
  for_ 0 (toU n) fun k => do
    let b ← let_ (o + k * 5)
    let so ← let_ (load data b)
    let sc ← let_ (rgba (b + 1))
    if_ (t <=. so) do
      let span ← let_ (so - prevOff.get)
      let kk ← let_ (select (span <=. 0) 0 ((t - prevOff.get) / span))
      ret (mix4 prevCol.get sc kk)
    prevOff.set so
    prevCol.set sc
  ret prevCol.get

def sampleStops := sampleStopsDef.2

/-- A field of primitive `base` (`prims[base + k]`). -/
def field (base : Expr .u32) (k : Nat) : Expr .f32 := load prims (base + .litU k.toUInt32)

/-- Color of primitive `base`'s paint at local point `q`. -/
def paintAtDef := Fn.def2 "paint_at" .u32 .v2 .v4 fun base q => do
  let kind ← let_ (field base 24)
  if_ (kind ==. 0) (ret (vec4 (field base 28) (field base 29) (field base 30) (field base 31)))
  let g0 ← let_ (vec2 (field base 32) (field base 33))
  let t ← var_ (0 : Expr .f32)
  if_ (kind ==. 1)
    (do
      let d ← let_ (vec2 (field base 34) (field base 35) - g0)
      let l2 ← let_ (dot d d)
      t.set (select (l2 ==. 0) 0 (dot (q - g0) d / l2)))
    (do
      let r ← let_ (field base 34)
      t.set (select (r ==. 0) 0 (length (q - g0) / r)))
  ret (sampleStops (field base 25) (field base 26) t.get)

def paintAt := paintAtDef.2

/-! ### Coverage per primitive kind -/

/-- Analytic shape: distance in local space, optionally turned into a stroke. -/
def shapeCoverageDef := Fn.def2 "shape_coverage" .u32 .v2 .f32 fun base q => do
  let shape ← let_ (field base 1)
  let a ← let_ (vec4 (field base 16) (field base 17) (field base 18) (field base 19))
  let dl ← var_ (0 : Expr .f32)
  if_ (shape ==. 0) (dl.set (sdRoundedBox q (vec2 (comp a 0) (comp a 1)) (vec2 (comp a 2) (comp a 3))
    (vec4 (field base 20) (field base 21) (field base 22) (field base 23))))
  if_ (shape ==. 1) (dl.set (sdCircle q (vec2 (comp a 0) (comp a 1)) (comp a 2)))
  if_ (shape ==. 2) (dl.set (sdEllipse q (vec2 (comp a 0) (comp a 1)) (comp a 2) (comp a 3)))
  if_ (shape ==. 3) (dl.set (sdSegment q (vec2 (comp a 0) (comp a 1)) (vec2 (comp a 2) (comp a 3))))
  let mode ← let_ (field base 2)
  let hw ← let_ (field base 3)
  let d ← let_ (select (mode ==. 1) (abs dl.get - hw) (select (mode ==. 2) (dl.get - hw) dl.get))
  ret (coverage (d * field base 14))

/-- Blurred rounded box (`RenderOp.shadow`), with the CPU's exact cut-offs. -/
def shadowCoverageDef := Fn.def2 "shadow_coverage" .u32 .v2 .f32 fun base q => do
  let d ← let_ (sdRoundedBox q (vec2 (field base 16) (field base 17))
    (vec2 (field base 18) (field base 19))
    (vec4 (field base 20) (field base 21) (field base 22) (field base 23)) * field base 14)
  let sigma ← let_ (field base 15)
  if_ (sigma <=. 0) (ret (coverage d))
  let edge ← let_ (4 * sigma + 0.5)
  if_ (d >=. edge) (ret (0 : Expr .f32))
  if_ (d <=. -edge) (ret (1 : Expr .f32))
  ret (0.5 * (1 - erf (d / (sigma * 1.41421356237))))

/-- `Raster.fillPolys` for the pixel whose top-left corner is `(px, py)`. -/
def pathFillCoverageDef := Fn.def3 "path_fill_coverage" .u32 .f32 .f32 .f32
    fun base px py => do
  let off ← let_ (toU (field base 16))
  let n ← let_ (toU (field base 17))
  let evenOdd ← let_ (field base 18 ==. 1)
  let right ← let_ (px + 1)
  let acc ← var_ (0 : Expr .f32)
  for_ 0 4 fun s => do
    let sy ← let_ (py + (toF s + 0.5) / 4)
    -- winding number just right of the pixel's left edge
    let wind ← var_ (0 : Expr .f32)
    for_ 0 n fun e => do
      let b ← let_ (off + e * 5)
      let y0 ← let_ (load data (b + 1))
      let y1 ← let_ (load data (b + 3))
      if_ ((y0 <=. sy) &&. (sy <. y1)) do
        let x0 ← let_ (load data b)
        let xc ← let_ (x0 + (sy - y0) * (load data (b + 2) - x0) / (y1 - y0))
        if_ (xc <=. px) (wind.set (wind.get + load data (b + 4)))
    -- walk the crossings inside the pixel from left to right
    let cur ← var_ px
    for_ 0 32 fun _ => do
      let nx ← var_ right
      let nd ← var_ (0 : Expr .f32)
      for_ 0 n fun e => do
        let b ← let_ (off + e * 5)
        let y0 ← let_ (load data (b + 1))
        let y1 ← let_ (load data (b + 3))
        if_ ((y0 <=. sy) &&. (sy <. y1)) do
          let x0 ← let_ (load data b)
          let xc ← let_ (x0 + (sy - y0) * (load data (b + 2) - x0) / (y1 - y0))
          if_ ((xc >. cur.get) &&. (xc <. right)) do
            if_ (xc <. nx.get)
              (do nx.set xc; nd.set (load data (b + 4)))
              (if_ (xc ==. nx.get) (nd.set (nd.get + load data (b + 4))))
      let aw ← let_ (abs wind.get)
      let inside ← let_ (select evenOdd (aw - 2 * floor (aw / 2) !=. 0) (wind.get !=. 0))
      if_ inside (acc.set (acc.get + (nx.get - cur.get) * 0.25))
      if_ (nx.get >=. right) break_
      wind.set (wind.get + nd.get)
      cur.set nx.get
  ret (Expr.min acc.get 1)

/-- `Raster.strokePolys`: distance to the flattened polyline (device space). -/
def pathStrokeCoverageDef := Fn.def2 "path_stroke_coverage" .u32 .v2 .f32 fun base p => do
  let off ← let_ (toU (field base 16))
  let n ← let_ (toU (field base 17))
  let d ← var_ (1.0e30 : Expr .f32)
  for_ 0 n fun e => do
    let b ← let_ (off + e * 5)
    d.set (Expr.min d.get (sdSegment p (vec2 (load data b) (load data (b + 1)))
      (vec2 (load data (b + 2)) (load data (b + 3)))))
  ret (coverage (d.get - field base 3))

/-- `Raster.drawText` for one glyph: exact area coverage of its lit cells. -/
def glyphCoverageDef := Fn.def3 "glyph_coverage" .u32 .f32 .f32 .f32 fun base px py => do
  let sc ← let_ (field base 3)
  let gx ← let_ (field base 16)
  let oy ← let_ (field base 17)
  let lo ← let_ (toU (field base 18))
  let hi ← let_ (toU (field base 19))
  let cov ← var_ (0 : Expr .f32)
  for_ 0 7 fun j => do
    let jf ← let_ (toF j)
    let vy ← let_ (overlap py (py + 1) (oy + jf * sc) (oy + (jf + 1) * sc))
    if_ (vy >. 0) do
      let bits ← let_ (band (select (j <. 4) (shr lo (j * 5)) (shr hi ((j - 4) * 5))) 31)
      for_ 0 5 fun i => do
        if_ (band (shr bits (4 - i)) 1 ==. 1) do
          let f ← let_ (toF i)
          cov.set (cov.get + vy * overlap px (px + 1) (gx + f * sc) (gx + (f + 1) * sc))
  ret (Expr.min cov.get 1)

def shapeCoverage := shapeCoverageDef.2
def shadowCoverage := shadowCoverageDef.2
def pathFillCoverage := pathFillCoverageDef.2
def pathStrokeCoverage := pathStrokeCoverageDef.2
def glyphCoverage := glyphCoverageDef.2

/-- Color (straight alpha, coverage folded into alpha) of primitive `i` at the
pixel whose center is `p`. -/
def shadeDef := Fn.def2 "shade" .u32 .v2 .v4 fun i p => do
  let base ← let_ (i * .litU primStride.toUInt32)
  let kind ← let_ (field base 0)
  -- local coordinates through the inverse transform (slots 8..13)
  let q ← let_ (vec2 (field base 8 * x p + field base 10 * y p + field base 12)
    (field base 9 * x p + field base 11 * y p + field base 13))
  let px ← let_ (floor (x p))
  let py ← let_ (floor (y p))
  let cov ← var_ (0 : Expr .f32)
  if_ (kind ==. litN kindShape) (cov.set (shapeCoverage base q))
  if_ (kind ==. litN kindShadow) (cov.set (shadowCoverage base q))
  if_ (kind ==. litN kindPathFill) (cov.set (pathFillCoverage base px py))
  if_ (kind ==. litN kindPathStroke) (cov.set (pathStrokeCoverage base p))
  if_ (kind ==. litN kindGlyph) (cov.set (glyphCoverage base px py))
  if_ (cov.get <=. 0) (ret (vec4 0 0 0 0))
  let col ← let_ (paintAt base q)
  ret (vec4 (comp col 0) (comp col 1) (comp col 2) (comp col 3 * cov.get))

/-- Every function of the module, callees first. -/
def functions : List FnDef :=
  [sdCircleDef.1, sdRoundedBoxDef.1, sdSegmentDef.1, sdEllipseDef.1, erfDef.1, overlapDef.1,
   sampleStopsDef.1, paintAtDef.1, shapeCoverageDef.1, shadowCoverageDef.1,
   pathFillCoverageDef.1, pathStrokeCoverageDef.1, glyphCoverageDef.1, shadeDef.1]

/-- Bindings and entry points around the generated functions. The vertex stage
expands primitive `i` into the two triangles of its pixel rectangle (slots
4..7, device pixels); the fragment stage calls `shade`. -/
def skeleton : String := "
@group(0) @binding(0) var<storage, read> prims : array<f32>;
@group(0) @binding(1) var<storage, read> data : array<f32>;
@group(0) @binding(2) var<uniform> screen : vec4f;

struct VOut {
  @builtin(position) pos : vec4f,
  @location(0) @interpolate(flat) prim : u32,
};

@vertex fn vs(@builtin(vertex_index) v : u32, @builtin(instance_index) i : u32) -> VOut {
  let base = i * " ++ toString primStride ++ "u;
  let ux = select(0.0, 1.0, v == 1u || v == 4u || v == 5u);
  let uy = select(0.0, 1.0, v == 2u || v == 3u || v == 5u);
  let px = mix(prims[base + 4u], prims[base + 6u], ux);
  let py = mix(prims[base + 5u], prims[base + 7u], uy);
  var out : VOut;
  out.pos = vec4f(px / screen.x * 2.0 - 1.0, 1.0 - py / screen.y * 2.0, 0.0, 1.0);
  out.prim = i;
  return out;
}

@fragment fn fs(in : VOut) -> @location(0) vec4f {
  return shade(in.prim, in.pos.xy);
}
"

/-- The complete WGSL module of the GPU renderer. -/
def shaderSource : String :=
  "// Generated by UVL (GPU/Kernels.lean). Do not edit.\n" ++ skeleton ++ "\n" ++
    "\n".intercalate (functions.map FnDef.toWGSL)

end UVL.GPU
