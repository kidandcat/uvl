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

/-- Run `app` in a desktop window until it is closed.

Frames are rendered only when something changed (or every frame while the app
is animating), so an idle UI costs no CPU.

For headless smoke tests: `UVL_MAX_FRAMES=n` exits after `n` presented frames,
`UVL_SCREENSHOT=file.png` saves the last presented frame on exit, and
`UVL_CLICK_TARGET=i` clicks the centre of tap target `i` through SDL's event
queue after the first frame. When rendering on the GPU, the screenshot step
also reads back what the GPU draws for the last frame and fails if it differs
from the CPU frame by more than float rounding. `UVL_RENDERER=cpu` disables the
GPU renderer. -/
partial def run (app : App Model Msg) (w : Nat := 800) (h : Nat := 600) : IO Unit := do
  let maxFrames := (← IO.getEnv "UVL_MAX_FRAMES").bind String.toNat?
  let screenshot ← IO.getEnv "UVL_SCREENSHOT"
  let clickTarget := (← IO.getEnv "UVL_CLICK_TARGET").bind String.toNat?
  openWindow app.title w.toUInt32 h.toUInt32
  let gpu ← gpuInit GPU.shaderSource Native.GPU.entries
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
  let rec loop (rt : Runtime Model Msg) (last : UInt64) (frames : Nat)
      (lastArea : Option Window := none) : IO Unit := do
    let raw ← pollRaw
    let now ← ticksMs
    let mut rt := rt.step raw (now - last).toNat.toF
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
      if gpu then
        discard <| Native.GPU.draw rt.width rt.height rt.ops rt.app.background
        rt := { rt with dirty := false }
      else
        rt := rt.present
        present rt.pixels rt.width.toUInt32 rt.height.toUInt32
      frames := frames + 1
      if frames == 1 then
        if let some i := clickTarget then
          if let some t := rt.targets[i]? then
            pushClick (t.x + t.w / 2).toF (t.y + t.h / 2).toF
    if let some m := maxFrames then
      if frames ≥ m then finish rt; return
    -- a blinking caret alone only needs a frame every half period
    if rt.app.animating rt.model || rt.hoverFade < 1 then wait 1
    else if rt.animating then wait 50
    else wait 250
    loop rt now frames area
  loop (Runtime.start app w h) (← ticksMs) 0

end UVL.SDL
