import UVL.App.Runtime
import UVL.GPU.Batch

/-!
# Host interface

What a platform shell (SDL window, browser, …) needs from the runtime, in a
form that crosses a C ABI easily:

* **Packed events.** Shells deliver input as a flat `FloatArray`, 5 floats per
  event: `[kind, a, b, c, d]`.

  | kind | event        | a, b, c               |
  |------|--------------|-----------------------|
  | 1    | pointer move | x, y                  |
  | 2    | pointer down | x, y, button          |
  | 3    | pointer up   | x, y, button          |
  | 4    | scroll       | dx, dy                |
  | 5    | key down     | keycode               |
  | 6    | key up       | keycode               |
  | 7    | text input   | Unicode codepoint     |
  | 8    | resize       | width, height         |
  | 9    | quit         |                       |
  | 10   | pointer leave|                       |

  Keycodes follow SDL: printable keys are their codepoint, arrows are
  `0x4000004F` (right) to `0x40000052` (up).

* **`AnyRuntime`**, a runtime with its model and message types hidden, plus
  `@[export]`ed `step`/`frame` functions so a C shell can drive any app
  without knowing its types. All exported functions take their arguments owned
  (the C caller must `lean_inc` anything it keeps).
-/

namespace UVL

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

/-- Decode a packed event buffer (see the module docs). -/
def decodeEvents (raw : FloatArray) : Array Event := Id.run do
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

namespace Runtime

variable {Model Msg : Type}

/-- One shell iteration: apply the packed events, then advance animations by
`dtMs` milliseconds when the app is animating. -/
def step (rt : Runtime Model Msg) (raw : FloatArray) (dtMs : Float) : Runtime Model Msg :=
  let rt := (decodeEvents raw).foldl handle rt
  if rt.app.animating rt.model then
    { rt.handle (.tick (dtMs / 1000.0)) with dirty := true }
  else rt

end Runtime

/-- A runtime whose model and message types are hidden, so that a C shell can
hold any app as one opaque object. -/
structure AnyRuntime where
  {Model : Type}
  {Msg : Type}
  rt : Runtime Model Msg

namespace AnyRuntime

def start {Model Msg : Type} (app : App Model Msg) (w h : UInt32) : AnyRuntime :=
  ⟨Runtime.start app w.toNat h.toNat⟩

@[export uvl_host_step]
def step (r : AnyRuntime) (raw : FloatArray) (dtMs : Float) : AnyRuntime :=
  ⟨r.rt.step raw dtMs⟩

/-- Does the shell need to present a new frame? -/
@[export uvl_host_dirty]
def dirty (r : AnyRuntime) : UInt8 := if r.rt.dirty then 1 else 0

@[export uvl_host_quit]
def quit (r : AnyRuntime) : UInt8 := if r.rt.quit then 1 else 0

@[export uvl_host_width]
def width (r : AnyRuntime) : UInt32 := r.rt.width.toUInt32

@[export uvl_host_height]
def height (r : AnyRuntime) : UInt32 := r.rt.height.toUInt32

/-- RGBA8 pixels of the current frame (`width * height * 4` bytes). -/
@[export uvl_host_frame]
def frame (r : AnyRuntime) : ByteArray := r.rt.frame

/-- Render the current frame incrementally and clear `dirty` (see
`Runtime.present`). Pass the only reference so the frame is updated in place. -/
@[export uvl_host_present]
def present (r : AnyRuntime) : AnyRuntime := ⟨r.rt.present⟩

/-- RGBA8 pixels of the last `present`. -/
@[export uvl_host_pixels]
def pixels (r : AnyRuntime) : ByteArray := r.rt.pixels

/-- Windows repainted by the last `present`, as `x, y, w, h` quadruples. -/
@[export uvl_host_damage]
def damage (r : AnyRuntime) : FloatArray :=
  r.rt.damage.foldl (init := .empty) fun a d =>
    a.push d.x.toF |>.push d.y.toF |>.push d.w.toF |>.push d.h.toF

/-- The current frame lowered to GPU primitives (see `GPU/Batch.lean`). -/
@[export uvl_host_gpu_batch]
def gpuBatch (r : AnyRuntime) : GPU.Batch := GPU.Batch.build r.rt.width r.rt.height r.rt.ops

/-- Background color as `r, g, b, a` in `[0, 1]`. -/
@[export uvl_host_background]
def background (r : AnyRuntime) : FloatArray :=
  let c := r.rt.app.background
  FloatArray.empty.push c.r |>.push c.g |>.push c.b |>.push c.a

/-- Forget the presented frame and request a complete new one (after the shell
switches between GPU and CPU rendering). -/
@[export uvl_host_invalidate]
def invalidate (r : AnyRuntime) : AnyRuntime := ⟨{ r.rt with dirty := true, presented := none }⟩

@[export uvl_host_mark_clean]
def markClean (r : AnyRuntime) : AnyRuntime := ⟨{ r.rt with dirty := false }⟩

/-- Centre of tap target `i`, for scripted smoke tests (`#[]` if absent). -/
@[export uvl_host_target_center]
def targetCenter (r : AnyRuntime) (i : UInt32) : FloatArray :=
  match r.rt.targets[i.toNat]? with
  | some t => (FloatArray.empty.push (t.x + t.w / 2).toFloat).push (t.y + t.h / 2).toFloat
  | none => .empty

end AnyRuntime

namespace GPU.Batch

@[export uvl_gpu_batch_prims] def primsOf (b : Batch) : FloatArray := b.prims
@[export uvl_gpu_batch_data] def dataOf (b : Batch) : FloatArray := b.data
@[export uvl_gpu_batch_count] def countOf (b : Batch) : UInt32 := b.count.toUInt32

end GPU.Batch

/-- WGSL source of the GPU renderer (`GPU/Kernels.lean`). -/
@[export uvl_gpu_shader] def gpuShader (_ : Unit) : String := GPU.shaderSource

/-- Fragment entry points of the GPU renderer, comma-separated, indexed by
primitive kind (slot 0 of a record). -/
@[export uvl_gpu_entry_points] def gpuEntryPoints (_ : Unit) : String :=
  ",".intercalate GPU.kindEntryPoints

end UVL
