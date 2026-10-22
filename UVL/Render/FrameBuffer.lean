import UVL.Core.Color

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

namespace UVL

theorem ByteArray.size_set' (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) :
    (a.set i v h).size = a.size := by
  show (a.set i v h).data.size = a.data.size
  rw [ByteArray.data_set]; exact Array.size_set ..

theorem ByteArray.size_uset (a : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < a.size) :
    (a.uset i v h).size = a.size := by
  cases a
  simp [ByteArray.uset, ByteArray.size]

private theorem four_lt_usize : 4 < USize.size :=
  Nat.lt_of_lt_of_le (by decide : (4 : Nat) < 2 ^ 32) USize.le_size

/-- `n < USize.size` without building `2^numBits`. On 64-bit that power is not a
64-bit word, and the bare-metal runtime rejects it. `n >>> 32 < 2^32` is `n < 2^64`. -/
private def fitsUSize (n : Nat) : Bool :=
  if System.Platform.numBits == 64 then n >>> 32 < 4294967296 else n < 4294967296

private theorem two32 : 2 ^ 32 = 4294967296 := by decide

private theorem fitsUSize_lt (n : Nat) (h : fitsUSize n = true) : n < USize.size := by
  rw [USize.size_eq_two_pow]
  unfold fitsUSize at h
  cases System.Platform.numBits_eq with
  | inl hbits =>
    simp only [hbits] at h
    have hne : ((32 == 64) = false) := by decide
    simp only [hne] at h
    have hn : n < 4294967296 := of_decide_eq_true h
    simpa [two32, hbits] using hn
  | inr hbits =>
    simp only [hbits] at h
    have heq : ((64 == 64) = true) := by decide
    simp only [heq, ite_true] at h
    have hq : n >>> 32 < 4294967296 := of_decide_eq_true h
    rw [Nat.shiftRight_eq_div_pow, ← two32] at hq
    have hmul : n < 2 ^ 32 * 2 ^ 32 := (Nat.div_lt_iff_lt_mul (by decide)).mp hq
    have hpow : 2 ^ 32 * 2 ^ 32 = 2 ^ 64 := by rw [← Nat.pow_add]
    simpa [hbits, hpow] using hmul

private theorem usize_toNat_add (i : USize) (n : Nat) (hn : n < USize.size)
    (h : i.toNat + n < USize.size) : (i + OfNat.ofNat n).toNat = i.toNat + n := by
  rw [USize.toNat_add, USize.toNat_ofNat_of_lt hn, Nat.mod_eq_of_lt h]

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

/-- `n` copies of pixel `p`, one byte at a time. Fallback for `fillPixels`. -/
def fillPixelsSlow (n : Nat) (p : RGBA8) : { b : ByteArray // b.size = n * 4 } :=
  go 0 (ByteArray.emptyWithCapacity (n * 4)) rfl (Nat.zero_le _)
where
  go (i : Nat) (b : ByteArray) (hb : b.size = i * 4) (hi : i ≤ n) :
      { b : ByteArray // b.size = n * 4 } :=
    if hlt : i < n then
      go (i + 1) (b.push p.r |>.push p.g |>.push p.b |>.push p.a)
        (by simp only [ByteArray.size_push, hb]; omega) hlt
    else ⟨b, by rw [hb, Nat.le_antisymm hi (Nat.le_of_not_lt hlt)]⟩
  termination_by n - i

/-- `n` copies of pixel `p` by doubling a 4-byte seed (`copySlice` is a memcpy).
The result has length `n * 4` when the doubling reaches the target, and is
shorter only if a step cannot grow — `fillPixels` then uses `fillPixelsSlow`. -/
def replicatePixels (n : Nat) (p : RGBA8) : ByteArray :=
  if n == 0 then ByteArray.empty else
  let target := n * 4
  let seed := ByteArray.empty.push p.r |>.push p.g |>.push p.b |>.push p.a
  let rec go (fuel : Nat) (b : ByteArray) : ByteArray :=
    match fuel with
    | 0 => b
    | fuel + 1 =>
      if b.size >= target then b else
      let add := Min.min b.size (target - b.size)
      if add == 0 then b else
      -- append a prefix of `b` (a fresh array, so the copy does not overlap)
      go fuel (b ++ b.extract 0 add)
  (go target seed).extract 0 target

/-- `n` copies of pixel `p`, with the size proved. -/
def fillPixels (n : Nat) (p : RGBA8) : { b : ByteArray // b.size = n * 4 } :=
  let b := replicatePixels n p
  if h : b.size = n * 4 then ⟨b, h⟩ else fillPixelsSlow n p

/-- A buffer filled with a single color. -/
def new (w h : Nat) (bg : Color := Color.transparent) : FrameBuffer w h :=
  let ⟨b, hb⟩ := fillPixels (w * h) bg.toRGBA8
  ⟨b, hb⟩

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

/-- One channel of a source-over blend. Not a local closure: those are boxed
per call, and this runs once per covered pixel. -/
@[inline] def mixChannel (sa da oa s : Float) (dv : UInt8) : UInt8 :=
  Color.toByte ((s * sa + (dv.toFloat / 255.0) * da * (1.0 - sa)) / oa)

/-- Source-over blend of `c` with fractional `coverage` onto pixel `(x, y)`. -/
@[inline] def blend (fb : FrameBuffer w h) (x : Fin w) (y : Fin h) (c : Color)
    (coverage : Float) : FrameBuffer w h :=
  let sa := Color.clamp01 (c.a * coverage)
  if sa <= 0.0 then fb else
  if sa >= 1.0 then fb.setPixel x y c.toRGBA8 else
  let d := fb.getPixel x y
  let da := d.a.toFloat / 255.0
  let oa := sa + da * (1.0 - sa)
  fb.setPixel x y ⟨mixChannel sa da oa c.r d.r, mixChannel sa da oa c.g d.g,
    mixChannel sa da oa c.b d.b, Color.toByte oa⟩

/-- Fold over `lo ≤ i < hi` where `hi ≤ n`, yielding indices as `Fin n`.
The only test performed is the loop condition itself. -/
@[specialize] def foldRange {n : Nat} {β : Type} (lo hi : Nat) (hhi : hi ≤ n) (init : β)
    (f : β → Fin n → β) : β :=
  let rec go (i : Nat) (acc : β) : β :=
    if hi' : i < hi then go (i + 1) (f acc ⟨i, Nat.lt_of_lt_of_le hi' hhi⟩) else acc
  termination_by hi - i
  go lo init

private theorem nat_le_four_lt_usize {n : Nat} (h : n ≤ 4) : n < USize.size :=
  Nat.lt_of_le_of_lt h four_lt_usize

/-- Write four channels at `i`. The length proof is erased; each `uset` is a store. -/
@[inline] def writePx (data : ByteArray) (i : USize) (p : RGBA8)
    (hs : i.toNat + 4 ≤ data.size) (hw : i.toNat + 4 < USize.size) :
    { b : ByteArray // b.size = data.size } :=
  have h0 : i.toNat < data.size := by omega
  let d0 := data.uset i p.r h0
  have s0 : d0.size = data.size := ByteArray.size_uset data i p.r h0
  have i1 : (i + 1).toNat = i.toNat + 1 :=
    usize_toNat_add i 1 (nat_le_four_lt_usize (by decide)) (by omega)
  have h1 : (i + 1).toNat < d0.size := by rw [s0, i1]; omega
  let d1 := d0.uset (i + 1) p.g h1
  have s1 : d1.size = data.size := (ByteArray.size_uset d0 (i + 1) p.g h1).trans s0
  have i2 : (i + 2).toNat = i.toNat + 2 :=
    usize_toNat_add i 2 (nat_le_four_lt_usize (by decide)) (by omega)
  have h2 : (i + 2).toNat < d1.size := by rw [s1, i2]; omega
  let d2 := d1.uset (i + 2) p.b h2
  have s2 : d2.size = data.size := (ByteArray.size_uset d1 (i + 2) p.b h2).trans s1
  have i3 : (i + 3).toNat = i.toNat + 3 :=
    usize_toNat_add i 3 (nat_le_four_lt_usize (by decide)) (by omega)
  have h3 : (i + 3).toNat < d2.size := by rw [s2, i3]; omega
  let d3 := d2.uset (i + 3) p.a h3
  ⟨d3, (ByteArray.size_uset d2 (i + 3) p.a h3).trans s2⟩

/-- Write pixel `p` over columns `[x0, x1)` of row `y`.

Fully covered opaque runs take this path. The index stays in a `USize` and each
store goes through `ByteArray.uset`, whose in-bounds proof is erased. There is
no second use of the buffer, so reference counting reuses it in place — a
fallback that still mentioned `fb` made the first store clone the whole frame.
-/
def blitSpan (fb : FrameBuffer w h) (y : Fin h) (x0 x1 : Nat) (p : RGBA8) : FrameBuffer w h :=
  if hle : x0 ≤ x1 ∧ x1 ≤ w then
    let nbytes := w * h * 4
    let span := x1 - x0
    let off := (y.val * w + x0) * 4
    have hoff : off + span * 4 ≤ nbytes := by
      have hy : y.val < h := y.isLt
      have hx0 : x0 ≤ x1 := hle.1
      have hx1 : x1 ≤ w := hle.2
      have hsum : (y.val * w + x0) * 4 + (x1 - x0) * 4 = (y.val * w + x1) * 4 := by omega
      rw [hsum]
      have hrow : y.val * w + x1 ≤ h * w := by
        calc
          y.val * w + x1 ≤ y.val * w + w := Nat.add_le_add_left hx1 _
          _ = (y.val + 1) * w := by rw [Nat.succ_mul]
          _ ≤ h * w := Nat.mul_le_mul_right _ hy
      calc
        (y.val * w + x1) * 4 ≤ (h * w) * 4 := Nat.mul_le_mul_right 4 hrow
        _ = w * h * 4 := by rw [Nat.mul_comm h w]
    -- one comparison per span, not per byte; the slow arm is unreachable for
    -- any framebuffer that fits in the address space
    if hfitB : fitsUSize nbytes then
      have husize : nbytes < USize.size := fitsUSize_lt nbytes hfitB
      let rec go (i : USize) (k : Nat) (data : ByteArray) (hsize : data.size = nbytes)
          (hi : i.toNat = off + k * 4) : { b : ByteArray // b.size = nbytes } :=
        if hlt : k < span then
          have hfitN : i.toNat + 4 ≤ nbytes := by rw [hi]; omega
          have hfit : i.toNat + 4 ≤ data.size := by rw [hsize]; exact hfitN
          have hwrap : i.toNat + 4 < USize.size := Nat.lt_of_le_of_lt hfitN husize
          let r := writePx data i p hfit hwrap
          have hi' : (i + 4).toNat = off + (k + 1) * 4 := by
            rw [usize_toNat_add i 4 four_lt_usize hwrap, hi]; omega
          go (i + 4) (k + 1) r.1 (r.2.trans hsize) hi'
        else
          ⟨data, hsize⟩
      termination_by (x1 - x0) - k
      have hoffU : off < USize.size :=
        Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right off (span * 4)) hoff) husize
      let r := go off.toUSize 0 fb.data fb.hsize (by
        have : off.toUSize.toNat = off := by
          rw [Nat.toUSize, USize.toNat_ofNat', ← USize.size_eq_two_pow]
          exact Nat.mod_eq_of_lt hoffU
        omega)
      ⟨r.1, r.2⟩
    else
      foldRange x0 x1 hle.2 fb fun fb xi => fb.setPixel xi y p
  else fb

/-- Read four channels at `i`. Proofs are erased; each `uget` is a load. -/
@[inline] def readPx (data : ByteArray) (i : USize)
    (hs : i.toNat + 4 ≤ data.size) (hw : i.toNat + 4 < USize.size) : RGBA8 :=
  have h0 : i.toNat < data.size := by omega
  have i1 : (i + 1).toNat = i.toNat + 1 :=
    usize_toNat_add i 1 (nat_le_four_lt_usize (by decide)) (by omega)
  have h1 : (i + 1).toNat < data.size := by rw [i1]; omega
  have i2 : (i + 2).toNat = i.toNat + 2 :=
    usize_toNat_add i 2 (nat_le_four_lt_usize (by decide)) (by omega)
  have h2 : (i + 2).toNat < data.size := by rw [i2]; omega
  have i3 : (i + 3).toNat = i.toNat + 3 :=
    usize_toNat_add i 3 (nat_le_four_lt_usize (by decide)) (by omega)
  have h3 : (i + 3).toNat < data.size := by rw [i3]; omega
  ⟨data.uget i h0, data.uget (i + 1) h1, data.uget (i + 2) h2, data.uget (i + 3) h3⟩

/-- Source-over blend of a constant color at coverage 1 over columns `[x0, x1)`.

Same bytes as `blend` at coverage 1. Opaque colors store `toRGBA8` through
`blitSpan`; translucent colors reuse one running index instead of recomputing
`(y * w + x) * 4` per pixel. -/
def blendSpan (fb : FrameBuffer w h) (y : Fin h) (x0 x1 : Nat) (c : Color) : FrameBuffer w h :=
  if hle : x0 ≤ x1 ∧ x1 ≤ w then
    let sa := Color.clamp01 c.a
    if sa <= 0.0 then fb else
    if sa >= 1.0 then fb.blitSpan y x0 x1 c.toRGBA8 else
    let inv := 1.0 - sa
    let sr := c.r * sa
    let sg := c.g * sa
    let sb := c.b * sa
    let nbytes := w * h * 4
    let span := x1 - x0
    let off := (y.val * w + x0) * 4
    have hoff : off + span * 4 ≤ nbytes := by
      have hy : y.val < h := y.isLt
      have hx0 : x0 ≤ x1 := hle.1
      have hx1 : x1 ≤ w := hle.2
      have hsum : (y.val * w + x0) * 4 + (x1 - x0) * 4 = (y.val * w + x1) * 4 := by omega
      rw [hsum]
      have hrow : y.val * w + x1 ≤ h * w := by
        calc
          y.val * w + x1 ≤ y.val * w + w := Nat.add_le_add_left hx1 _
          _ = (y.val + 1) * w := by rw [Nat.succ_mul]
          _ ≤ h * w := Nat.mul_le_mul_right _ hy
      calc
        (y.val * w + x1) * 4 ≤ (h * w) * 4 := Nat.mul_le_mul_right 4 hrow
        _ = w * h * 4 := by rw [Nat.mul_comm h w]
    if hfitB : fitsUSize nbytes then
      have husize : nbytes < USize.size := fitsUSize_lt nbytes hfitB
      let rec go (i : USize) (k : Nat) (data : ByteArray) (hsize : data.size = nbytes)
          (hi : i.toNat = off + k * 4) : { b : ByteArray // b.size = nbytes } :=
        if hlt : k < span then
          have hfitN : i.toNat + 4 ≤ nbytes := by rw [hi]; omega
          have hfit : i.toNat + 4 ≤ data.size := by rw [hsize]; exact hfitN
          have hwrap : i.toNat + 4 < USize.size := Nat.lt_of_le_of_lt hfitN husize
          let d := readPx data i hfit hwrap
          let da := d.a.toFloat / 255.0
          let oa := sa + da * inv
          let p : RGBA8 := ⟨
            Color.toByte ((sr + (d.r.toFloat / 255.0) * da * inv) / oa),
            Color.toByte ((sg + (d.g.toFloat / 255.0) * da * inv) / oa),
            Color.toByte ((sb + (d.b.toFloat / 255.0) * da * inv) / oa),
            Color.toByte oa⟩
          let r := writePx data i p hfit hwrap
          have hi' : (i + 4).toNat = off + (k + 1) * 4 := by
            rw [usize_toNat_add i 4 four_lt_usize hwrap, hi]; omega
          go (i + 4) (k + 1) r.1 (r.2.trans hsize) hi'
        else
          ⟨data, hsize⟩
      termination_by (x1 - x0) - k
      have hoffU : off < USize.size :=
        Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right off (span * 4)) hoff) husize
      let r := go off.toUSize 0 fb.data fb.hsize (by
        have : off.toUSize.toNat = off := by
          rw [Nat.toUSize, USize.toNat_ofNat', ← USize.size_eq_two_pow]
          exact Nat.mod_eq_of_lt hoffU
        omega)
      ⟨r.1, r.2⟩
    else
      foldRange x0 x1 hle.2 fb fun fb xi => fb.blend xi y c 1.0
  else fb

end FrameBuffer

end UVL
