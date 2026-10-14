import UVL.GPU.Kernels
import UVL.Render.Raster

/-!
# Lowering render ops to GPU primitives

`Batch.build w h ops` walks the scene with the same context as the CPU
rasterizer (transform, integer clip rectangle) and emits, in paint order, one
primitive per shape, shadow, path or glyph. A primitive is a `primStride`-float
record in `prims` (layout below) whose pixel rectangle is exactly the set of
pixels the CPU rasterizer would visit for that op; paths and gradients put
their flattened edges and color stops in `data`.

Record layout (`GPU/Kernels.lean` reads the same slots):

| slots  | meaning                                                          |
|--------|------------------------------------------------------------------|
| 0      | kind (`kindShape`, `kindShadow`, `kindPathFill`, …)              |
| 1      | shape: 0 rounded box, 1 circle, 2 ellipse, 3 segment             |
| 2      | distance mode: 0 fill, 1 `abs d - hw` (stroke), 2 `d - hw`        |
| 3      | half stroke width (local; device for paths) or glyph scale        |
| 4–7    | pixel rectangle `x0 y0 x1 y1` (device pixels)                     |
| 8–13   | inverse transform `a b c d e f` (device → local)                  |
| 14     | transform scale factor                                           |
| 15     | blur (device px)                                                 |
| 16–19  | shape parameters / data offset and count / glyph position, bits  |
| 20–23  | corner radii / MSDF pen position and size                         |
| 24–26  | paint kind (0 solid, 1 linear, 2 radial), stop offset, count     |
| 28–31  | solid color                                                      |
| 32–35  | gradient geometry                                                |

MSDF glyphs read their texels from a third buffer, the atlas, which persists
across frames: a batch names the atlas it uses and the glyphs it draws
(`atlasGlyphs`), and the host uploads each glyph's cell the first time it shows
up. One atlas per frame is supported; glyphs of any other atlas are skipped.
-/

namespace UVL.GPU

open Raster

/-- Primitives and their side data, ready to upload. -/
structure Batch where
  prims : FloatArray := .empty
  data : FloatArray := .empty
  count : Nat := 0
  /-- The MSDF atlas the batch draws from, if any. -/
  atlas : Option MSDF.Atlas := none
  /-- Atlas glyphs drawn by the batch, in order of first use. -/
  atlasGlyphs : Array Nat := #[]
deriving Inhabited

/-- A primitive record before packing. -/
structure Prim where
  kind : Nat
  shape : Nat := 0
  mode : Nat := 0
  hw : Float := 0
  inv : Affine := {}
  scale : Float := 1
  blur : Float := 0
  a : V4 := ⟨0, 0, 0, 0⟩
  radii : SDF.Corners := {}

namespace Batch

/-- Append the paint's stops to `data`; returns slots 24..35. -/
def paintSlots (b : Batch) (p : Paint) : Batch × Array Float :=
  let stops (b : Batch) (ss : Array Stop) : Batch × Float :=
    let off := b.data.size.toF
    (ss.foldl (init := b) fun b (o, c) =>
      { b with data := b.data.push o |>.push c.r |>.push c.g |>.push c.b |>.push c.a }, off)
  match p with
  | .solid c => (b, #[0, 0, 0, 0, c.r, c.g, c.b, c.a, 0, 0, 0, 0])
  | .linear p0 p1 ss =>
    let (b, off) := stops b ss
    (b, #[1, off, ss.size.toF, 0, 0, 0, 0, 0, p0.x, p0.y, p1.x, p1.y])
  | .radial c r ss =>
    let (b, off) := stops b ss
    (b, #[2, off, ss.size.toF, 0, 0, 0, 0, 0, c.x, c.y, r, 0])

/-- Append a primitive covering the pixels of `clip` (nothing if empty). -/
def push {w h : Nat} (b : Batch) (clip : Clip w h) (pr : Prim) (paint : Paint) : Batch :=
  if clip.x1 ≤ clip.x0 || clip.y1 ≤ clip.y0 then b else
  let (b, ps) := b.paintSlots paint
  let m := pr.inv
  let rec_ : Array Float :=
    #[pr.kind.toF, pr.shape.toF, pr.mode.toF, pr.hw,
      clip.x0.toF, clip.y0.toF, clip.x1.toF, clip.y1.toF,
      m.a, m.b, m.c, m.d, m.e, m.f, pr.scale, pr.blur,
      pr.a.x, pr.a.y, pr.a.z, pr.a.w,
      pr.radii.tl, pr.radii.tr, pr.radii.br, pr.radii.bl] ++ ps
  { b with prims := rec_.foldl FloatArray.push b.prims, count := b.count + 1 }

/-- Shape number and parameters (slots 1, 16..23) of an analytic shape. -/
def shapeParams : Shape → Option (Nat × V4 × SDF.Corners × Rect)
  | .rect r => some (0, ⟨r.center.x, r.center.y, r.w / 2, r.h / 2⟩, {}, r)
  | .roundedRect r rad => some (0, ⟨r.center.x, r.center.y, r.w / 2, r.h / 2⟩, rad, r)
  | .circle c r => some (1, ⟨c.x, c.y, r, 0⟩, {}, ⟨c.x - r, c.y - r, 2 * r, 2 * r⟩)
  | .ellipse c rx ry => some (2, ⟨c.x, c.y, rx, ry⟩, {}, ⟨c.x - rx, c.y - ry, 2 * rx, 2 * ry⟩)
  | .line a b => some (3, ⟨a.x, a.y, b.x, b.y⟩, {}, Rect.ofPoints #[a, b])
  | .path .. => none

/-- Append `n` records of 5 floats to `data`; returns their offset. -/
def pushData (b : Batch) (recs : Array (Float × Float × Float × Float × Float)) : Batch × Float :=
  let off := b.data.size.toF
  ({ b with data := recs.foldl (init := b.data) fun d (p, q, r, s, t) =>
      d.push p |>.push q |>.push r |>.push s |>.push t }, off)

/-- Rows per band of a path primitive. Each band only carries the edges that
can affect its pixels, so the per-pixel loops of the path kernels stay short
for large paths. -/
def bandRows : Nat := 8

/-- Split `clip` into bands of `bandRows` rows and run `f b y0 y1 band` for
each band `[y0, y1)`. -/
def bands {w h : Nat} (clip : Clip w h) (b : Batch)
    (f : Batch → Nat → Nat → Clip w h → Batch) : Batch :=
  if clip.x1 ≤ clip.x0 || clip.y1 ≤ clip.y0 then b else
  (List.range ((clip.y1 - clip.y0 + bandRows - 1) / bandRows)).foldl (init := b) fun b k =>
    let y0 := clip.y0 + k * bandRows
    let y1 := Min.min clip.y1 (y0 + bandRows)
    f b y0 y1 { clip with y0, y1, hy := Nat.le_trans (Nat.min_le_left _ _) clip.hy }

/-- Lower one op (mirrors `Raster.renderOp`). -/
partial def op {w h : Nat} (ctx : Ctx w h) (b : Batch) : RenderOp → Batch
  | .fill (.path p rule) paint =>
    let polys := p.flatten ctx.m
    let edges := edgesOf polys
    if edges.isEmpty then b else
    let bbox := Rect.ofPoints (polys.foldl (fun acc p => acc ++ p.pts) #[])
    bands (ctx.clipTo (bbox.inflate 1.0)) b fun b y0 y1 band =>
      -- the edges that cross some sub-scanline of rows `[y0, y1)`
      let es := edges.filter fun e => e.y1 > y0.toF && e.y0 < y1.toF
      if es.isEmpty then b else
      let (b, off) := b.pushData (es.map fun e => (e.x0, e.y0, e.x1, e.y1, Float.ofInt e.dir))
      b.push band
        { kind := kindPathFill, inv := ctx.m.inverse,
          a := ⟨off, es.size.toF, if rule == .evenOdd then 1 else 0, 0⟩ } paint
  | .fill s paint =>
    match shapeParams s with
    | some (shape, a, radii, bbox) =>
      b.push (ctx.clipTo ((ctx.m.mapRect bbox).inflate 1.0))
        { kind := kindShape, shape, inv := ctx.m.inverse, scale := ctx.m.scaleFactor, a, radii }
        paint
    | none => b
  | .stroke (.path p _) width paint =>
    let polys := p.flatten ctx.m
    let hw := width * ctx.m.scaleFactor / 2.0
    let segs : Array (Vec2 × Vec2) := polys.foldl (init := #[]) fun acc poly =>
      let n := poly.pts.size
      let k := if poly.closed then n else n - 1
      (Array.range k).foldl (init := acc) fun acc i =>
        acc.push (poly.pts[i]!, poly.pts[(i + 1) % n]!)
    if segs.isEmpty then b else
    let bbox := (Rect.ofPoints (polys.foldl (fun acc p => acc ++ p.pts) #[])).inflate (hw + 1.0)
    bands (ctx.clipTo bbox) b fun b y0 y1 band =>
      -- segments farther than `hw + 1` from the band cannot cover its pixels
      let ss := segs.filter fun (p, q) =>
        Min.min p.y q.y - hw - 1.0 <= y1.toF && Max.max p.y q.y + hw + 1.0 >= y0.toF
      if ss.isEmpty then b else
      let (b, off) := b.pushData (ss.map fun (p, q) => (p.x, p.y, q.x, q.y, 0))
      b.push band
        { kind := kindPathStroke, hw, inv := ctx.m.inverse, a := ⟨off, ss.size.toF, 0, 0⟩ } paint
  | .stroke s width paint =>
    match shapeParams s with
    | some (shape, a, radii, bbox) =>
      -- lines offset the distance (`d - w/2`); closed shapes stroke both sides (`|d| - w/2`)
      let mode := if shape == 3 then 2 else 1
      b.push (ctx.clipTo ((ctx.m.mapRect (bbox.inflate (width / 2.0))).inflate 1.0))
        { kind := kindShape, shape, mode, hw := width / 2.0, inv := ctx.m.inverse,
          scale := ctx.m.scaleFactor, a, radii } paint
    | none => b
  | .shadow r radius blur c =>
    let blur := blur * ctx.m.scaleFactor
    b.push (ctx.clipTo ((ctx.m.mapRect r).inflate (1.0 + 4.0 * blur)))
      { kind := kindShadow, inv := ctx.m.inverse, scale := ctx.m.scaleFactor, blur,
        a := ⟨r.center.x, r.center.y, r.w / 2, r.h / 2⟩, radii := .all radius } (.solid c)
  | .text pos s scale c =>
    let o := ctx.m.apply pos
    let sc := scale * ctx.m.scaleFactor
    let chars := s.toList.toArray
    (Array.range chars.size).foldl (init := b) fun b k =>
      let g := Font.glyph chars[k]!
      let row (j : Nat) : Nat := g[j]?.getD 0
      let lo := row 0 + row 1 * 32 + row 2 * 1024 + row 3 * 32768
      let hi := row 4 + row 5 * 32 + row 6 * 1024
      if lo == 0 && hi == 0 then b else
      let gx := o.x + (k * Font.advance).toF * sc
      b.push (ctx.clipTo ⟨gx, o.y, 5.0 * sc, 7.0 * sc⟩)
        { kind := kindGlyph, hw := sc, a := ⟨gx, o.y, lo.toF, hi.toF⟩ } (.solid c)
  | .glyphs atlas quads paint =>
    if b.atlas.any (·.id != atlas.id) then b else
    quads.foldl (init := { b with atlas := some atlas }) fun b q =>
      let c := atlas.cell q.glyph
      if c.w <= 0 then b else
      let b := if MSDF.hasNat b.atlasGlyphs q.glyph then b
        else { b with atlasGlyphs := b.atlasGlyphs.push q.glyph }
      b.push (ctx.clipTo ((ctx.m.mapRect (atlas.quadRect q)).inflate 1.0))
        { kind := kindMSDF, inv := ctx.m.inverse, scale := ctx.m.scaleFactor,
          a := ⟨(q.glyph * MSDF.cellFloats).toF, c.x, c.y, c.texel⟩,
          radii := ⟨q.x, q.y, q.size, 0⟩ } paint
  | .transform m ops => ops.foldl (op { ctx with m := ctx.m.compose m }) b
  | .clip r ops => ops.foldl (op { ctx with clip := ctx.clipTo (ctx.m.mapRect r) }) b
  | .group ops => ops.foldl (op ctx) b

/-- Size in floats of the atlas buffer the batch needs (0 without MSDF glyphs). -/
def atlasSize (b : Batch) : Nat := (b.atlas.map (·.cells.size)).getD 0 * MSDF.cellFloats

/-- The atlas buffer with the cells of the batch's glyphs filled in (the rest
zero). Hosts upload cells incrementally instead; this is for tests. -/
def atlasData (b : Batch) : FloatArray := Id.run do
  let some a := b.atlas | return .empty
  let mut out := FloatArray.mk (Array.replicate b.atlasSize 0)
  for g in b.atlasGlyphs do
    let tex := a.glyphTexels g
    for k in [0:tex.size] do
      out := out.set! (g * MSDF.cellFloats + k) tex[k]!
  return out

/-- Gaps shorter than this many floats between two changed ranges are
re-uploaded too (one write instead of two). -/
def mergeGap : Nat := 64

/-- At most this many ranges; beyond that they collapse into one. -/
def maxRanges : Nat := 32

/-- The float ranges `[start, stop)` of `new` that differ from `old`, flattened
as `start₀ stop₀ start₁ stop₁ …`: what to write when the GPU buffer already
holds `old`. Floats past the end of `old` count as changed. -/
def changedRanges (old new : FloatArray) : FloatArray := Id.run do
  let mut rs : Array (Nat × Nat) := #[]
  let mut i := 0
  while i < new.size do
    if i < old.size && old[i]!.toBits == new[i]!.toBits then
      i := i + 1
    else
      let mut j := i + 1
      while j < new.size && !(j < old.size && old[j]!.toBits == new[j]!.toBits) do j := j + 1
      rs := match rs.back? with
        | some (s, e) => if i - e < mergeGap then rs.pop.push (s, j) else rs.push (i, j)
        | none => rs.push (i, j)
      i := j
  if rs.size > maxRanges then
    rs := #[(rs[0]!.1, rs[rs.size - 1]!.2)]
  return rs.foldl (fun a (s, e) => a.push s.toFloat |>.push e.toFloat) .empty

/-- Number of floats covered by `changedRanges` output. -/
def rangesSize (rs : FloatArray) : Nat := Id.run do
  let mut n := 0
  for k in [0:rs.size / 2] do
    n := n + (rs[2 * k + 1]!.toUInt64.toNat - rs[2 * k]!.toUInt64.toNat)
  return n

/-- Lower a `w × h` scene. -/
def build (w h : Nat) (ops : Array RenderOp) : Batch :=
  ops.foldl (op (w := w) (h := h) { clip := Clip.full w h }) {}

end Batch

end UVL.GPU
