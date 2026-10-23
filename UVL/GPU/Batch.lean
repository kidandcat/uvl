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

Sprites read their texels from the `tex` buffer the same way: one texture per
frame, uploaded when it changes (sprites of any other texture are skipped).

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
  /-- The sprite texture the batch draws from, if any. -/
  texture : Option Texture := none
  /-- Lower sprites to hardware-sampled instanced quads (`kindSpriteRun`
  markers plus records in `sprites`) instead of per-sprite uber primitives.
  Off by default: the interpreted reference renderer and the web host only
  know the uber primitives. -/
  instanced : Bool := false
  /-- Instance records of the frame's dynamic sprite runs,
  `spriteStride` floats each (see `pushInstance`). -/
  sprites : FloatArray := .empty
  /-- Static layers drawn this frame, in order of first use; a run's source
  slot names its layer as `index + 1`. -/
  layers : Array SpriteLayer := #[]
  /-- Primitives `[0, split)` are the world, drawn into the scaled offscreen
  target, the rest (the HUD) at native resolution (`buildSplit`). 0 = no
  split. -/
  split : Nat := 0
  /-- Size of the scaled world target (when `split > 0`). -/
  worldW : Nat := 0
  worldH : Nat := 0
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

/-! The arrays are taken out of the batch before appending (`takePrims`,
`takeData`): `{ b with prims := b.prims.push x }` would push onto an array
still shared with `b`, copying it on every primitive. -/

@[inline] def takePrims (b : Batch) : FloatArray × Batch := (b.prims, { b with prims := .empty })
@[inline] def takeData (b : Batch) : FloatArray × Batch := (b.data, { b with data := .empty })
@[inline] def takeSprites (b : Batch) : FloatArray × Batch := (b.sprites, { b with sprites := .empty })

/-- Append the paint's stops to `data`; returns slots 24..35. -/
def paintSlots (b : Batch) (p : Paint) : Batch × Array Float :=
  let stops (b : Batch) (ss : Array Stop) : Batch × Float :=
    let off := b.data.size.toF
    let (d, b) := b.takeData
    let d := ss.foldl (init := d) fun d (o, c) =>
      d.push o |>.push c.r |>.push c.g |>.push c.b |>.push c.a
    ({ b with data := d }, off)
  match p with
  | .solid c => (b, #[0, 0, 0, 0, c.r, c.g, c.b, c.a, 0, 0, 0, 0])
  | .linear p0 p1 ss =>
    let (b, off) := stops b ss
    (b, #[1, off, ss.size.toF, 0, 0, 0, 0, 0, p0.x, p0.y, p1.x, p1.y])
  | .radial c r ss =>
    let (b, off) := stops b ss
    (b, #[2, off, ss.size.toF, 0, 0, 0, 0, 0, c.x, c.y, r, 0])

/-- Append a primitive covering the pixels of `clip` (nothing if empty), with
slots 24..35 given. -/
def pushSlots {w h : Nat} (b : Batch) (clip : Clip w h) (pr : Prim) (ps : Array Float) : Batch :=
  if clip.x1 ≤ clip.x0 || clip.y1 ≤ clip.y0 then b else
  let m := pr.inv
  let (p, b) := b.takePrims
  let p := p.push pr.kind.toF |>.push pr.shape.toF |>.push pr.mode.toF |>.push pr.hw
    |>.push clip.x0.toF |>.push clip.y0.toF |>.push clip.x1.toF |>.push clip.y1.toF
    |>.push m.a |>.push m.b |>.push m.c |>.push m.d |>.push m.e |>.push m.f
    |>.push pr.scale |>.push pr.blur
    |>.push pr.a.x |>.push pr.a.y |>.push pr.a.z |>.push pr.a.w
    |>.push pr.radii.tl |>.push pr.radii.tr |>.push pr.radii.br |>.push pr.radii.bl
  { b with prims := ps.foldl FloatArray.push p, count := b.count + 1 }

/-- Floats per instance record: `dst x y w h`, `src x y w h` (texels),
opacity, smooth, 0, 0. -/
def spriteStride : Nat := 12

/-- Append one instance record to `sprites`. -/
@[inline] def pushInstance (out : FloatArray) (s : Sprite) (smooth : Bool) : FloatArray :=
  out.push s.dst.x |>.push s.dst.y |>.push s.dst.w |>.push s.dst.h
    |>.push s.src.x |>.push s.src.y |>.push s.src.w |>.push s.src.h
    |>.push s.opacity |>.push (if smooth then 1 else 0) |>.push 0 |>.push 0

/-- Append a `kindSpriteRun` marker: `count` instances starting at `first` (for a layer, any nonzero `count`: the host draws all it uploaded)
of source `source` (0 = `sprites`, `i + 1` = `layers[i]`), drawn with the
forward transform `m` and scissored to `clip`. Slots: 4–7 clip, 8–13 forward
transform `a b c d e f`, 16 source, 17 first, 18 count, 19–20 texture size. -/
def pushRun {w h : Nat} (b : Batch) (clip : Clip w h) (m : Affine) (tex : Texture)
    (source first count : Nat) : Batch :=
  if count == 0 || clip.x1 ≤ clip.x0 || clip.y1 ≤ clip.y0 then b else
  let (p, b) := b.takePrims
  let p := p.push kindSpriteRun.toF |>.push 0 |>.push 0 |>.push 0
    |>.push clip.x0.toF |>.push clip.y0.toF |>.push clip.x1.toF |>.push clip.y1.toF
    |>.push m.a |>.push m.b |>.push m.c |>.push m.d |>.push m.e |>.push m.f
    |>.push 0 |>.push 0
    |>.push source.toF |>.push first.toF |>.push count.toF |>.push tex.w.toF |>.push tex.h.toF
  let p := (List.range (primStride - 21)).foldl (fun p _ => p.push 0) p
  { b with prims := p, count := b.count + 1 }

/-- Append a primitive covering the pixels of `clip` (nothing if empty). -/
def push {w h : Nat} (b : Batch) (clip : Clip w h) (pr : Prim) (paint : Paint) : Batch :=
  if clip.x1 ≤ clip.x0 || clip.y1 ≤ clip.y0 then b else
  let (b, ps) := b.paintSlots paint
  b.pushSlots clip pr ps

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
  let (d, b) := b.takeData
  let d := recs.foldl (init := d) fun d (p, q, r, s, t) =>
    d.push p |>.push q |>.push r |>.push s |>.push t
  ({ b with data := d }, off)

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

-- Same well-founded measure as `Raster.renderOp`: a child is smaller than the
-- array, and the array is smaller than the container.
mutual

/-- Lower `ops[i:]` (mirrors `Raster.renderArray`). -/
def opArray {w h : Nat} (ctx : Ctx w h) (ops : Array RenderOp) (i : Nat) (b : Batch) : Batch :=
  if h : i < ops.size then
    opArray ctx ops (i + 1) (op ctx b ops[i])
  else
    b
termination_by (sizeOf ops, ops.size - i)

/-- Lower one op (mirrors `Raster.renderOp`). -/
def op {w h : Nat} (ctx : Ctx w h) (b : Batch) (o : RenderOp) : Batch :=
  match o with
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
      let ch := chars[k]!
      let row (j : Nat) : Nat := Font.glyphRow ch j
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
  | .sprites tex quads smooth =>
    if b.texture.any (·.id != tex.id) then b else
    if b.instanced then
      let first := b.sprites.size / spriteStride
      let (sp, b) := b.takeSprites
      let sp := quads.foldl (init := sp) fun sp s =>
        if s.src.w <= 0 || s.src.h <= 0 || s.opacity <= 0 then sp else pushInstance sp s smooth
      let n := sp.size / spriteStride - first
      pushRun { b with sprites := sp, texture := some tex } ctx.clip ctx.m tex 0 first n
    else
    let inv := ctx.m.inverse
    let scale := ctx.m.scaleFactor
    quads.foldl (init := { b with texture := some tex }) fun b s =>
      if s.src.w <= 0 || s.src.h <= 0 || s.opacity <= 0 then b else
      let p := s.params
      b.pushSlots (ctx.clipTo ((ctx.m.mapRect s.dst).inflate 1.0))
        { kind := kindSprite, inv, scale, a := ⟨p.cx, p.cy, p.hx, p.hy⟩,
          radii := ⟨p.dx, p.dy, p.ku, p.kv⟩ }
        #[p.sx, p.sy, p.sw, p.sh, tex.w.toF, if smooth then 1 else 0, s.opacity, 0, 0, 0, 0, 0]
  | .layer l =>
    if b.texture.any (·.id != l.tex.id) then b else
    if b.instanced then
      let (b, idx) := match b.layers.findIdx? (·.key == l.key) with
        | some i => (b, i)
        | none => ({ b with layers := b.layers.push l }, b.layers.size)
      pushRun { b with texture := some l.tex } ctx.clip ctx.m l.tex (idx + 1) 0 1
    else
    let inv := ctx.m.inverse
    let scale := ctx.m.scaleFactor
    let tex := l.tex
    l.quads.get.foldl (init := { b with texture := some tex }) fun b s =>
      if s.src.w <= 0 || s.src.h <= 0 || s.opacity <= 0 then b else
      let p := s.params
      b.pushSlots (ctx.clipTo ((ctx.m.mapRect s.dst).inflate 1.0))
        { kind := kindSprite, inv, scale, a := ⟨p.cx, p.cy, p.hx, p.hy⟩,
          radii := ⟨p.dx, p.dy, p.ku, p.kv⟩ }
        #[p.sx, p.sy, p.sw, p.sh, tex.w.toF, if l.smooth then 1 else 0, s.opacity, 0, 0, 0, 0, 0]
  | .transform m ops => opArray { ctx with m := ctx.m.compose m } ops 0 b
  | .clip r ops => opArray { ctx with clip := ctx.clipTo (ctx.m.mapRect r) } ops 0 b
  | .group ops => opArray ctx ops 0 b
termination_by (sizeOf o, 0)

end

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

/-- The texture's texels as `u32`s (`tex` buffer), for the interpreted
reference renderer (hosts upload the bytes as they are). -/
def texData (b : Batch) : FloatArray := Id.run do
  let some t := b.texture | return .empty
  let n := t.w * t.h
  let mut out := FloatArray.emptyWithCapacity n
  for i in [0:n] do
    let byte (k : Nat) : Float := (t.pixels.get! (4 * i + k)).toFloat
    out := out.push (byte 0 + 256 * (byte 1 + 256 * (byte 2 + 256 * byte 3)))
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
def build (w h : Nat) (ops : Array RenderOp) (instanced := false) : Batch :=
  ops.foldl (op (w := w) (h := h) { clip := Clip.full w h }) { instanced }

/-- Size of the world target for a `w`-px-wide screen drawn at scale `k`. -/
def scaledSize (w h : Nat) (k : Float) : Nat × Nat :=
  if k >= 1 then (w, h) else
  (max 1 (w.toF * k).ceil.toUInt64.toNat, max 1 (h.toF * k).ceil.toUInt64.toNat)

/-- Lower a `w × h` frame whose `world` is drawn at scale `k ≤ 1` into a
smaller target (upscaled by the host) and whose `hud` is drawn at native
resolution on top. Both use the screen's coordinates. With `k ≥ 1` the frame
is lowered unsplit. -/
def buildSplit (w h : Nat) (k : Float) (world hud : Array RenderOp)
    (instanced := true) : Batch :=
  if k >= 1 then build w h (world ++ hud) instanced else
  let (ww, wh) := scaledSize w h k
  let sx := ww.toF / w.toF
  let sy := wh.toF / h.toF
  let b := op (w := ww) (h := wh) { clip := Clip.full ww wh } { instanced }
    (.transform (Affine.scale sx sy) world)
  let split := b.count
  let b := hud.foldl (op (w := w) (h := h) { clip := Clip.full w h }) b
  { b with split := if split == 0 then 0 else split, worldW := ww, worldH := wh }

end Batch

end UVL.GPU
