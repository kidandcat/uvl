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
  `0x4000004F` (right) to `0x40000052` (up), Shift is `0x400000E1` and Ctrl
  (or Cmd) `0x400000E0`. Consecutive text events are merged into one
  `textInput`, so pasted text (delivered one codepoint per event) is a single
  edit.

* **Clipboard.** After a step, the shell takes the text to copy with
  `uvl_host_take_clipboard` and puts it on the system clipboard. Pasting is
  the shell's job: it turns Ctrl+V (or the browser's paste event) into text
  events.

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
  | 0x4000004A => .home
  | 0x4000004D => .end_
  | 0x400000E1 | 0x400000E5 => .shift
  | 0x400000E0 | 0x400000E4 | 0x400000E3 | 0x400000E7 => .ctrl
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
    match ev, out.back? with
    | some (.textInput s), some (Event.textInput t) => out := out.pop.push (.textInput (t ++ s))
    | some e, _ => out := out.push e
    | none, _ => pure ()
  return out

namespace Runtime

variable {Model Msg : Type}

/-- One shell iteration: apply the packed events, then advance animations by
`dtMs` milliseconds when anything is animating (`Runtime.animating`). -/
def step (rt : Runtime Model Msg) (raw : FloatArray) (dtMs : Float) : Runtime Model Msg :=
  let rt := (decodeEvents raw).foldl handle rt
  if rt.animating then rt.handle (.tick (dtMs / 1000.0)) else rt

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

/-- Text to put on the system clipboard (`""` for none), and the runtime with
it cleared. Returns a pair so the C shell can keep the runtime unshared. -/
@[export uvl_host_take_clipboard]
def takeClipboard (r : AnyRuntime) : String × AnyRuntime :=
  let (c, rt) := r.rt.takeClipboard
  (c.getD "", ⟨rt⟩)

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

/-- The MSDF atlas the batch draws from: its id plus one, or 0 for none. -/
@[export uvl_gpu_batch_atlas_id] def atlasIdOf (b : Batch) : UInt32 :=
  match b.atlas with
  | some a => (a.id + 1).toUInt32
  | none => 0

/-- Size of the atlas buffer, in floats. -/
@[export uvl_gpu_batch_atlas_size] def atlasSizeOf (b : Batch) : UInt32 := b.atlasSize.toUInt32

/-- Atlas glyphs the batch draws (as floats). -/
@[export uvl_gpu_batch_atlas_glyphs] def atlasGlyphsOf (b : Batch) : FloatArray :=
  b.atlasGlyphs.foldl (fun a g => a.push g.toFloat) .empty

/-- Texels of atlas glyph `g` (`MSDF.cellFloats` floats, uploaded at
`g * MSDF.cellFloats`). -/
@[export uvl_gpu_batch_atlas_cell] def atlasCellOf (b : Batch) (g : UInt32) : FloatArray :=
  match b.atlas with
  | some a => a.glyphTexels g.toNat
  | none => .empty

end GPU.Batch

/-- Float ranges of `new` that differ from `old` (`Batch.changedRanges`). -/
@[export uvl_gpu_changed_ranges] def gpuChangedRanges (old new : FloatArray) : FloatArray :=
  GPU.Batch.changedRanges old new

/-- Floats per MSDF atlas cell. -/
@[export uvl_gpu_atlas_cell_floats] def gpuCellFloats (_ : Unit) : UInt32 := MSDF.cellFloats.toUInt32

/-- WGSL source of the GPU renderer (`GPU/Kernels.lean`). -/
@[export uvl_gpu_shader] def gpuShader (_ : Unit) : String := GPU.shaderSource

/-- Fragment entry points of the GPU renderer, comma-separated, indexed by
primitive kind (slot 0 of a record). -/
@[export uvl_gpu_entry_points] def gpuEntryPoints (_ : Unit) : String :=
  ",".intercalate GPU.kindEntryPoints

end UVL
