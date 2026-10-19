import UVL

/-!
# Desktop GPU renderer (wgpu-native)

Lean bindings for `native/gpu_shell.c`, which draws the primitives of
`GPU/Batch.lean` with the WGSL program of `GPU/Kernels.lean` through
wgpu-native's `webgpu.h`: the same renderer as the browser's, on Vulkan, Metal
or D3D12. The SDL shell (`UVLWindow.lean`) uses it for windows; headless
rendering (offscreen, with read-back) serves the tests.
-/

namespace UVL.Native.GPU

/-- Initialize without a window: frames are drawn offscreen and read back. -/
@[extern "uvl_gpu_init_headless"]
opaque initHeadless (wgsl entries : @& String) : IO Bool

/-- Draw primitives (`GPU.Batch`) onto the window surface and present them, or,
headless or with `readback`, offscreen; then returns the RGBA pixels (empty
when presenting to a window). -/
@[extern "uvl_gpu_draw"]
opaque drawRaw (prims data primRanges dataRanges : @& FloatArray) (full : Bool)
  (count w h : UInt32) (bg : @& FloatArray) (readback : Bool) : IO ByteArray

/-- Bytes of primitives and data written to the GPU by the last draw. -/
@[extern "uvl_gpu_uploaded_bytes"]
opaque uploadedBytes : IO UInt64

/-- Replace the MSDF atlas buffer by a zeroed one of `floats` floats. -/
@[extern "uvl_gpu_atlas_reset"]
opaque atlasReset (floats : UInt32) : IO Unit

/-- Upload one atlas cell at float offset `offset`. -/
@[extern "uvl_gpu_atlas_write"]
opaque atlasWrite (offset : UInt32) (texels : @& FloatArray) : IO Unit

/-- Replace the sprite texture buffer by these RGBA8 texels. -/
@[extern "uvl_gpu_texture_upload"]
opaque textureUpload (pixels : @& ByteArray) : IO Unit

/-- Name of the GPU in use. -/
@[extern "uvl_gpu_adapter_name"]
opaque adapterName : IO String

/-- The fragment entry points, in primitive-kind order. -/
def entries : String := ",".intercalate GPU.kindEntryPoints

def initHeadless' : IO Bool := initHeadless GPU.shaderSource entries

/-- The atlas on the GPU (its id plus one, 0 for none) and the glyphs uploaded. -/
initialize atlasState : IO.Ref (Nat × Array Bool) ← IO.mkRef (0, #[])

/-- Upload the cells of the batch's MSDF glyphs that are not on the GPU yet
(recreating the atlas buffer when the batch uses another atlas). -/
def syncAtlas (b : GPU.Batch) : IO Unit := do
  let some a := b.atlas | return
  let (id, up) ← atlasState.get
  let mut up := up
  if id != a.id + 1 then
    atlasReset b.atlasSize.toUInt32
    up := Array.replicate a.cells.size false
  for g in b.atlasGlyphs do
    if !(up[g]?.getD true) then
      atlasWrite (g * MSDF.cellFloats).toUInt32 (a.glyphTexels g)
      up := up.set! g true
  atlasState.set (a.id + 1, up)

/-- The sprite texture on the GPU: its id plus one, 0 for none. -/
initialize textureState : IO.Ref Nat ← IO.mkRef 0

/-- Upload the batch's sprite texture unless it is already on the GPU. -/
def syncTexture (b : GPU.Batch) : IO Unit := do
  let some t := b.texture | return
  if (← textureState.get) != t.id + 1 then
    textureUpload t.pixels
    textureState.set (t.id + 1)

/-- The arrays of the previous frame, now on the GPU: only what changed since
is written (`Batch.changedRanges`). -/
initialize lastFrame : IO.Ref (Option (FloatArray × FloatArray)) ← IO.mkRef none

/-- Draw a lowered `w × h` scene on the GPU. -/
def drawBatch (b : GPU.Batch) (w h : Nat) (bg : Color) (readback : Bool := false) :
    IO ByteArray := do
  syncAtlas b
  syncTexture b
  let (pr, dr, full) := match ← lastFrame.get with
    | some (p, d) => (GPU.Batch.changedRanges p b.prims, GPU.Batch.changedRanges d b.data, false)
    | none => (.empty, .empty, true)
  lastFrame.set (some (b.prims, b.data))
  drawRaw b.prims b.data pr dr full b.count.toUInt32 w.toUInt32 h.toUInt32
    (FloatArray.empty.push bg.r |>.push bg.g |>.push bg.b |>.push bg.a) readback

/-- Lower a `w × h` scene and draw it on the GPU. -/
def draw (w h : Nat) (ops : Array RenderOp) (bg : Color) (readback : Bool := false) :
    IO ByteArray :=
  drawBatch (GPU.Batch.build w h ops) w h bg readback

end UVL.Native.GPU
