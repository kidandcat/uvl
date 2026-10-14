import UVL

/-!
# SDL3 desktop shell

A thin platform runner: SDL3 (via a ~150-line C shim in `native/sdl_shell.c`)
opens a window, delivers raw events and presents an RGBA buffer. Everything
else (state, layout, hit testing, rasterization) is the pure Lean runtime.
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
/-- Push a synthetic left click into SDL's event queue (for smoke tests). -/
@[extern "uvl_sdl_push_click"] opaque pushClick (x y : Float) : IO Unit

def keyOf (code : Nat) : Key :=
  match code with
  | 0x0D => .enter
  | 0x1B => .escape
  | 0x08 => .backspace
  | 0x09 => .tab
  | 0x7F => .delete
  | 0x4000004F => .right
  | 0x40000050 => .left
  | 0x40000051 => .down
  | 0x40000052 => .up
  | c => if 0x20 ≤ c && c < 0x110000 then .char (Char.ofNat c) else .other c

def buttonOf (b : Float) : MouseButton :=
  match b.toUInt64.toNat with
  | 1 => .left
  | 2 => .middle
  | 3 => .right
  | n => .other n

/-- Decode the packed event buffer produced by the C shim. -/
def decode (raw : FloatArray) : Array Event := Id.run do
  let mut out := #[]
  for i in [0:raw.size / 5] do
    let k := raw[5 * i]!.toUInt64.toNat
    let a := raw[5 * i + 1]!
    let b := raw[5 * i + 2]!
    let c := raw[5 * i + 3]!
    let ev : Option Event := match k with
      | 1 => some (.pointerMove a b)
      | 2 => some (.pointerDown a b (buttonOf c))
      | 3 => some (.pointerUp a b (buttonOf c))
      | 4 => some (.scroll a b)
      | 5 => some (.keyDown (keyOf a.toUInt64.toNat))
      | 6 => some (.keyUp (keyOf a.toUInt64.toNat))
      | 7 => some (.textInput (String.singleton (Char.ofNat a.toUInt64.toNat)))
      | 8 => some (.resize a.toUInt64.toNat b.toUInt64.toNat)
      | 9 => some .quit
      | 10 => some .pointerLeave
      | _ => none
    if let some e := ev then out := out.push e
  return out

variable {Model Msg : Type}

/-- Run `app` in a desktop window until it is closed.

Frames are rendered only when something changed (or every frame while the app
is animating), so an idle UI costs no CPU.

For headless smoke tests: `UVL_MAX_FRAMES=n` exits after `n` presented frames,
`UVL_SCREENSHOT=file.png` saves the last presented frame on exit, and
`UVL_CLICK_TARGET=i` clicks the centre of tap target `i` through SDL's event
queue after the first frame. -/
partial def run (app : App Model Msg) (w : Nat := 800) (h : Nat := 600) : IO Unit := do
  let maxFrames := (← IO.getEnv "UVL_MAX_FRAMES").bind String.toNat?
  let screenshot ← IO.getEnv "UVL_SCREENSHOT"
  let clickTarget := (← IO.getEnv "UVL_CLICK_TARGET").bind String.toNat?
  let finish (rt : Runtime Model Msg) : IO Unit := do
    if let some path := screenshot then IO.FS.writeBinFile path rt.framePNG
    close
  openWindow app.title w.toUInt32 h.toUInt32
  let rec loop (rt : Runtime Model Msg) (last : UInt64) (frames : Nat) : IO Unit := do
    let evs := decode (← pollRaw)
    let now ← ticksMs
    let mut rt := evs.foldl Runtime.handle rt
    if app.animating rt.model then
      rt := rt.handle (.tick ((now - last).toNat.toFloat / 1000.0))
      rt := { rt with dirty := true }
    if rt.quit then finish rt; return
    let mut frames := frames
    if rt.dirty then
      present rt.frame rt.width.toUInt32 rt.height.toUInt32
      rt := { rt with dirty := false }
      frames := frames + 1
      if frames == 1 then
        if let some i := clickTarget then
          if let some t := rt.targets[i]? then
            pushClick (t.x + t.w / 2).toFloat (t.y + t.h / 2).toFloat
    if let some m := maxFrames then
      if frames ≥ m then finish rt; return
    if !app.animating rt.model then wait 250 else wait 1
    loop rt now frames
  loop (Runtime.start app w h) (← ticksMs) 0

end UVL.SDL
