import UVLGPU
import Examples.Scenes
import Examples.Counter

/-!
`uvl-gpu-check`: render scenes with the desktop GPU renderer (headless,
wgpu-native) and compare the read-back pixels with the CPU rasterizer.
Exits with 1 if any scene differs by more than float rounding, 2 if no GPU is
available.
-/

open UVL

structure Scene where
  name : String
  w : Nat
  h : Nat
  ops : Array RenderOp
  bg : Color

def counterScene : Scene :=
  let rt := Runtime.start Examples.Counter.app 480 360
  ⟨"counter", 480, 360, rt.ops, rt.app.background⟩

def scenes : List Scene := [
  ⟨"primitives", 480, 320, Examples.primitives, Color.white⟩,
  ⟨"hello", 320, 160, Examples.hello.toOps 320 160, Color.hex 0xECEFF1⟩,
  ⟨"dashboard", 800, 600, Examples.dashboard.toOps 800 600, Color.hex 0xF5F7FA⟩,
  ⟨"typography", 460, 280, Examples.typography.toOps 460 280, Color.hex 0xECEFF1⟩,
  ⟨"msdf", 560, 260, Examples.msdfText, Color.white⟩,
  counterScene
]

/-- Largest channel error and channels off by more than 2. -/
def compare (gpu cpu : ByteArray) : Nat × Nat := Id.run do
  let mut mx := 0
  let mut over := 0
  for i in [0:Min.min gpu.size cpu.size] do
    if i % 4 != 3 then
      let d := ((gpu[i]!.toNat : Int) - cpu[i]!.toNat).natAbs
      if d > mx then mx := d
      if d > 2 then over := over + 1
  return (mx, over)

/-- Incremental uploads: a session of hovers and taps on the counter, each
frame drawn after the previous one (so only changed ranges are written) and
compared with the CPU. -/
def incremental : IO Bool := do
  let mut rt := Runtime.start Examples.Counter.app 480 360
  let pts := rt.targets.map fun t => ((t.x + t.w / 2).toF, (t.y + t.h / 2).toF)
  let (ax, ay) := pts[0]!; let (bx, by_) := pts[1]!
  let events : List Event := [.pointerMove ax ay, .pointerMove bx by_, .pointerDown bx by_ .left,
    .pointerUp bx by_ .left, .pointerLeave, .keyDown (.char '+'), .pointerMove ax ay]
  let mut ok := true
  let mut up := 0
  let mut total := 0
  for e in events do
    rt := rt.handle e
    let ops := rt.ops
    let gpu ← Native.GPU.draw 480 360 ops rt.app.background (readback := true)
    let b := GPU.Batch.build 480 360 ops
    up := up + (← Native.GPU.uploadedBytes).toNat
    total := total + 4 * (b.prims.size + b.data.size)
    let (mx, over) := compare gpu (Raster.render 480 360 ops rt.app.background).data
    ok := ok && over * 1000 ≤ gpu.size && mx ≤ 3
  let good := ok && up < total
  IO.println s!"  [{if good then "ok" else "FAIL"}] incremental: {events.length} counter frames match the CPU, {up} of {total} bytes uploaded"
  return good

def main : IO UInt32 := do
  unless ← Native.GPU.initHeadless' do
    IO.eprintln "uvl-gpu-check: no GPU (wgpu-native could not create a device)"
    return 2
  IO.println s!"adapter: {← Native.GPU.adapterName}"
  let mut ok := true
  for s in scenes do
    let t0 ← IO.monoNanosNow
    let gpu ← Native.GPU.draw s.w s.h s.ops s.bg (readback := true)
    let t1 ← IO.monoNanosNow
    let cpu := (Raster.render s.w s.h s.ops s.bg).data
    let (mx, over) := compare gpu cpu
    let good := gpu.size == cpu.size && over * 1000 ≤ cpu.size
    ok := ok && good
    IO.println s!"  [{if good then "ok" else "FAIL"}] {s.name} {s.w}x{s.h}: max channel error {mx}, {over} channels off by more than 2 (first frame incl. read-back {(t1 - t0).toFloat / 1e6} ms)"
  ok := (← incremental) && ok
  return if ok then 0 else 1
