import UniversalViz.Core.Color

/-!
# FrameBuffer

An RGBA8 pixel buffer whose dimensions live in its type. The invariant
`data.size = w * h * 4` is carried as a proof, so every pixel access below is
indexed by `Fin w × Fin h` and the byte offset is *proved* in bounds: there is
no runtime bounds check on the hot path and no way to write outside the buffer.

Thanks to Lean's reference counting with reuse (Perceus / FBIP), threading a
uniquely referenced `FrameBuffer` through the rasterizer mutates the underlying
`ByteArray` in place.
-/

namespace UViz

theorem ByteArray.size_set' (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) :
    (a.set i v h).size = a.size := by
  show (a.set i v h).data.size = a.data.size
  rw [ByteArray.data_set]; exact Array.size_set ..

/-- The byte offset of channel `c` of pixel `(x, y)` is inside a `w × h` RGBA buffer. -/
theorem pixel_index_lt {w h x y c : Nat} (hx : x < w) (hy : y < h) (hc : c < 4) :
    (y * w + x) * 4 + c < w * h * 4 := by
  have h1 : y * w + x < h * w := by
    have : y * w + x < (y + 1) * w := by rw [Nat.succ_mul]; omega
    exact Nat.lt_of_lt_of_le this (Nat.mul_le_mul_right _ hy)
  have h2 : (y * w + x) * 4 + c < (y * w + x + 1) * 4 := by rw [Nat.succ_mul]; omega
  have h3 : (y * w + x + 1) * 4 ≤ (h * w) * 4 := Nat.mul_le_mul_right _ h1
  rw [Nat.mul_comm w h]; omega

/-- 8-bit straight-alpha pixel. -/
structure RGBA8 where
  r : UInt8
  g : UInt8
  b : UInt8
  a : UInt8
deriving Inhabited, Repr, BEq

def Color.toRGBA8 (c : Color) : RGBA8 :=
  ⟨Color.toByte c.r, Color.toByte c.g, Color.toByte c.b, Color.toByte c.a⟩

structure FrameBuffer (w h : Nat) where
  data : ByteArray
  hsize : data.size = w * h * 4

namespace FrameBuffer

variable {w h : Nat}

/-- A buffer filled with a single color. -/
def new (w h : Nat) (bg : Color := Color.transparent) : FrameBuffer w h :=
  let p := bg.toRGBA8
  let arr := Array.ofFn (n := w * h * 4) fun i =>
    match i.val % 4 with
    | 0 => p.r | 1 => p.g | 2 => p.b | _ => p.a
  ⟨⟨arr⟩, by simp [ByteArray.size, arr]⟩

instance : Inhabited (FrameBuffer w h) := ⟨new w h⟩

@[inline] def idx (x : Fin w) (y : Fin h) (c : Nat) : Nat :=
  (y.val * w + x.val) * 4 + c

theorem idx_lt (fb : FrameBuffer w h) (x : Fin w) (y : Fin h) (c : Nat) (hc : c < 4) :
    idx x y c < fb.data.size := by
  rw [fb.hsize]; exact pixel_index_lt x.isLt y.isLt hc

@[inline] def setByte (fb : FrameBuffer w h) (i : Nat) (hi : i < w * h * 4) (v : UInt8) :
    FrameBuffer w h :=
  ⟨fb.data.set i v (by rw [fb.hsize]; exact hi),
   by rw [ByteArray.size_set']; exact fb.hsize⟩

@[inline] def getPixel (fb : FrameBuffer w h) (x : Fin w) (y : Fin h) : RGBA8 :=
  ⟨fb.data[idx x y 0]'(fb.idx_lt x y 0 (by decide)),
   fb.data[idx x y 1]'(fb.idx_lt x y 1 (by decide)),
   fb.data[idx x y 2]'(fb.idx_lt x y 2 (by decide)),
   fb.data[idx x y 3]'(fb.idx_lt x y 3 (by decide))⟩

@[inline] def setPixel (fb : FrameBuffer w h) (x : Fin w) (y : Fin h) (p : RGBA8) :
    FrameBuffer w h :=
  let fb := fb.setByte (idx x y 0) (pixel_index_lt x.isLt y.isLt (by decide)) p.r
  let fb := fb.setByte (idx x y 1) (pixel_index_lt x.isLt y.isLt (by decide)) p.g
  let fb := fb.setByte (idx x y 2) (pixel_index_lt x.isLt y.isLt (by decide)) p.b
  fb.setByte (idx x y 3) (pixel_index_lt x.isLt y.isLt (by decide)) p.a

/-- Source-over blend of `c` with fractional `coverage` onto pixel `(x, y)`. -/
@[inline] def blend (fb : FrameBuffer w h) (x : Fin w) (y : Fin h) (c : Color)
    (coverage : Float) : FrameBuffer w h :=
  let sa := Color.clamp01 (c.a * coverage)
  if sa <= 0.0 then fb else
  if sa >= 1.0 then fb.setPixel x y c.toRGBA8 else
  let d := fb.getPixel x y
  let da := d.a.toFloat / 255.0
  let oa := sa + da * (1.0 - sa)
  let mix (s : Float) (dv : UInt8) : UInt8 :=
    Color.toByte ((s * sa + (dv.toFloat / 255.0) * da * (1.0 - sa)) / oa)
  fb.setPixel x y ⟨mix c.r d.r, mix c.g d.g, mix c.b d.b, Color.toByte oa⟩

/-- Fold over `lo ≤ i < hi` where `hi ≤ n`, yielding indices as `Fin n`.
The only test performed is the loop condition itself. -/
@[specialize] def foldRange {n : Nat} {β : Type} (lo hi : Nat) (hhi : hi ≤ n) (init : β)
    (f : β → Fin n → β) : β :=
  let rec go (i : Nat) (acc : β) : β :=
    if hi' : i < hi then go (i + 1) (f acc ⟨i, Nat.lt_of_lt_of_le hi' hhi⟩) else acc
  termination_by hi - i
  go lo init

end FrameBuffer

end UViz
