import UVL
import UVLGPU

/-!
# SDL3 desktop shell

A thin platform runner: SDL3 (via a small C shim in `native/sdl_shell.c`)
opens a window and delivers raw events. Frames are drawn on the GPU by the
wgpu-native renderer (`UVLGPU.lean`) with the WGSL program Lean generates, or,
without a usable GPU, rasterized by Lean and presented as an RGBA buffer.
Everything else (state, layout, hit testing, lowering) is the pure Lean
runtime.
-/

namespace UVL.SDL

@[extern "uvl_sdl_open"] opaque openWindow (title : @& String) (w h : UInt32) : IO Unit
/-- Pending events, packed 5 floats each: `[kind, a, b, c, d]`. -/
@[extern "uvl_sdl_poll"] opaque pollRaw : IO FloatArray
@[extern "uvl_sdl_present"] opaque present (rgba : @& ByteArray) (w h : UInt32) : IO Unit
/-- Block until an event arrives or `timeoutMs` elapses. -/
@[extern "uvl_sdl_wait"] opaque wait (timeoutMs : UInt32) : IO Unit
@[extern "uvl_sdl_ticks"] opaque ticksMs : IO UInt64
@[extern "uvl_sdl_close"] opaque close : IO Unit
@[extern "uvl_sdl_set_clipboard"] opaque setClipboard (text : @& String) : IO Unit
@[extern "uvl_sdl_set_input_rect"] opaque setInputRect (x y w h : UInt32) : IO Unit
/-- Push a synthetic left click into SDL's event queue (for smoke tests). -/
@[extern "uvl_sdl_push_click"] opaque pushClick (x y : Float) : IO Unit
/-- Create the GPU renderer on the window; `false` means CPU frames. -/
@[extern "uvl_sdl_gpu_init"] opaque gpuInit (wgsl entries : @& String) : IO Bool

variable {Model Msg : Type}

/-- Frame timings accumulated for `UVL_STATS`, in nanoseconds. -/
structure Stats where
  since : Nat
  frames : Nat := 0
  /-- Events and app update (`Runtime.step`). -/
  step : Nat := 0
  /-- GPU: the view as render ops. CPU: view and rasterization (`Runtime.present`). -/
  view : Nat := 0
  /-- GPU: lowering to primitives. -/
  lower : Nat := 0
  /-- GPU: diffing, upload, submit and present. CPU: upload and present. -/
  present : Nat := 0

def Stats.report (s : Stats) (now : Nat) (gpu : Bool) : IO Unit := do
  let n := s.frames.toFloat
  let ms (v : Nat) : Float := (v.toFloat / n / 1e4).round / 100
  let fps := (n * 1e10 / (now - s.since).toFloat).round / 10
  IO.eprintln <| if gpu then
    s!"uvl: {fps} fps | per frame: step {ms s.step} ms, view {ms s.view} ms, " ++
      s!"lower {ms s.lower} ms, upload+submit+present {ms s.present} ms"
  else
    s!"uvl: {fps} fps | per frame: step {ms s.step} ms, view+raster {ms s.view} ms, " ++
      s!"upload+present {ms s.present} ms"

/-- Evaluate `x` before the next action (for timings). -/
@[noinline] def force {α : Type} (x : α) : IO α := pure x

/-- Run `app` in a desktop window until it is closed.

Frames are rendered only when something changed (or every frame while the app
is animating), so an idle UI costs no CPU.

For headless smoke tests: `UVL_MAX_FRAMES=n` exits after `n` presented frames,
`UVL_SCREENSHOT=file.png` saves the last presented frame on exit, and
`UVL_CLICK_TARGET=i` clicks the centre of tap target `i` through SDL's event
queue after the first frame. When rendering on the GPU, the screenshot step
also reads back what the GPU draws for the last frame and fails if it differs
from the CPU frame by more than float rounding. `UVL_RENDERER=cpu` disables the
GPU renderer.

For measuring: `UVL_STATS=1` never waits for events and prints the frame rate
and where the time goes every second. Combine it with `UVL_PRESENT=immediate`
(GPU) or `UVL_VSYNC=0` (CPU) to measure past the display refresh rate. -/
partial def run (app : App Model Msg) (w : Nat := 800) (h : Nat := 600) : IO Unit := do
  let maxFrames := (← IO.getEnv "UVL_MAX_FRAMES").bind String.toNat?
  let screenshot ← IO.getEnv "UVL_SCREENSHOT"
  let clickTarget := (← IO.getEnv "UVL_CLICK_TARGET").bind String.toNat?
  let stats := (← IO.getEnv "UVL_STATS").isSome
  openWindow app.title w.toUInt32 h.toUInt32
  let gpu ← gpuInit GPU.nativeShaderSource Native.GPU.entries
  if gpu then IO.eprintln s!"uvl: GPU renderer on {← Native.GPU.adapterName}"
  else IO.eprintln "uvl: CPU renderer"
  let finish (rt : Runtime Model Msg) : IO Unit := do
    if let some path := screenshot then
      IO.FS.writeBinFile path rt.framePNG
      if gpu then
        let px ← Native.GPU.draw rt.width rt.height rt.ops rt.app.background (readback := true)
        let cpu := rt.frame
        let over := (List.range cpu.size).foldl (init := 0) fun n i =>
          if i % 4 != 3 && ((px[i]!.toNat : Int) - cpu[i]!.toNat).natAbs > 2 then n + 1 else n
        IO.eprintln s!"uvl: GPU frame vs CPU frame: {over} channels off by more than 2"
        if px.size != cpu.size || over * 1000 > cpu.size then
          close
          throw <| IO.userError "GPU frame differs from the CPU frame"
    close
  let rec loop (rt : Runtime Model Msg) (last : UInt64) (frames : Nat) (st : Stats)
      (lastArea : Option Window := none) : IO Unit := do
    let t0 ← IO.monoNanosNow
    let raw ← pollRaw
    let now ← ticksMs
    let mut rt ← force (rt.step raw (now - last).toNat.toF)
    let t1 ← IO.monoNanosNow
    let mut st := { st with step := st.step + (t1 - t0) }
    if rt.quit then finish rt; return
    let (copied, rt') := rt.takeClipboard
    rt := rt'
    if let some text := copied then setClipboard text
    -- keep the IME candidate window next to the focused input
    let area := rt.inputRect
    if area != lastArea then
      if let some r := area then setInputRect r.x.toUInt32 r.y.toUInt32 r.w.toUInt32 r.h.toUInt32
    let mut frames := frames
    if rt.dirty then
      let t0 ← IO.monoNanosNow
      if gpu then
        let ops ← force rt.ops
        let t1 ← IO.monoNanosNow
        let b ← force (GPU.Batch.build rt.width rt.height ops (instanced := true))
        let t2 ← IO.monoNanosNow
        discard <| Native.GPU.drawBatch b rt.width rt.height rt.app.background
        let t3 ← IO.monoNanosNow
        st := { st with view := st.view + (t1 - t0), lower := st.lower + (t2 - t1),
                        present := st.present + (t3 - t2) }
        rt := { rt with dirty := false }
      else
        rt ← force rt.present
        let t1 ← IO.monoNanosNow
        present rt.pixels rt.width.toUInt32 rt.height.toUInt32
        let t2 ← IO.monoNanosNow
        st := { st with view := st.view + (t1 - t0), present := st.present + (t2 - t1) }
      frames := frames + 1
      st := { st with frames := st.frames + 1 }
      if frames == 1 then
        if let some i := clickTarget then
          if let some t := rt.targets[i]? then
            pushClick (t.x + t.w / 2).toF (t.y + t.h / 2).toF
    if let some m := maxFrames then
      if frames ≥ m then finish rt; return
    if stats then
      let t ← IO.monoNanosNow
      if t - st.since ≥ 1000000000 && st.frames > 0 then
        st.report t gpu
        st := { since := t }
    -- a blinking caret alone only needs a frame every half period
    else if rt.app.animating rt.model || rt.hoverFade < 1 then wait 1
    else if rt.animating then wait 50
    else wait 250
    loop rt now frames st area
  loop (Runtime.start app w h) (← ticksMs) 0 { since := ← IO.monoNanosNow }

end UVL.SDL
