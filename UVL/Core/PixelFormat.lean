import Std.Tactic.BVDecide
import UVL.Render.FrameBuffer

/-!
# Display pixel formats

Embedded displays rarely take RGBA8888:

* `RGB565`: 16 bits per pixel, the native format of SPI TFT controllers
  (ILI9341, ST7789, GC9A01). Sent big-endian (high byte first) over SPI.
* `Mono1Bit`: 1 bit per pixel for OLED / memory LCD panels (SSD1306, SH1106,
  Sharp Memory LCD), packed either SSD1306-style in vertical 8-pixel *pages* or
  row-major MSB-first.

The conversions are verified with `bv_decide` (exhaustive bit-blasting, checked
by the kernel through an LRAT certificate):

* quantization never leaves its bit field (`RGB565.q5_lt`, `RGB565.q6_lt`);
* `RGB565.encode ∘ RGB565.decode = id` on *all* 65536 values (`encode_decode`):
  a color that the panel can show survives the round trip through RGBA8 exactly;
* the rounding error of a channel is at most half a quantization step
  (`err5`, `err6`).
-/

namespace UVL

namespace RGB565

/-- Round an 8-bit channel to 5 bits: `round(v * 31 / 255)`. -/
@[inline] def q5 (v : UInt8) : UInt16 := (v.toUInt16 * 31 + 127) / 255
/-- Round an 8-bit channel to 6 bits: `round(v * 63 / 255)`. -/
@[inline] def q6 (v : UInt8) : UInt16 := (v.toUInt16 * 63 + 127) / 255
/-- Expand a 5-bit channel to 8 bits: `round(q * 255 / 31)`. -/
@[inline] def e5 (q : UInt16) : UInt8 := ((q * 255 + 15) / 31).toUInt8
/-- Expand a 6-bit channel to 8 bits: `round(q * 255 / 63)`. -/
@[inline] def e6 (q : UInt16) : UInt8 := ((q * 255 + 31) / 63).toUInt8

theorem q5_lt (v : UInt8) : q5 v < 32 := by unfold q5; bv_decide
theorem q6_lt (v : UInt8) : q6 v < 64 := by unfold q6; bv_decide
theorem q5_e5 (q : UInt16) (h : q < 32) : q5 (e5 q) = q := by unfold q5 e5; bv_decide
theorem q6_e6 (q : UInt16) (h : q < 64) : q6 (e6 q) = q := by unfold q6 e6; bv_decide

/-- Quantization error is at most half a 5-bit step (255 / 31 / 2 ≈ 4.1). -/
theorem err5 (v : UInt8) :
    (e5 (q5 v)).toUInt16 ≤ v.toUInt16 + 4 ∧ v.toUInt16 ≤ (e5 (q5 v)).toUInt16 + 4 := by
  unfold e5 q5; bv_decide
/-- Quantization error is at most half a 6-bit step (255 / 63 / 2 ≈ 2.0). -/
theorem err6 (v : UInt8) :
    (e6 (q6 v)).toUInt16 ≤ v.toUInt16 + 2 ∧ v.toUInt16 ≤ (e6 (q6 v)).toUInt16 + 2 := by
  unfold e6 q6; bv_decide

/-- Pack 8-bit RGB into `RRRRRGGGGGGBBBBB`. -/
@[inline] def encode (r g b : UInt8) : UInt16 := (q5 r <<< 11) ||| (q6 g <<< 5) ||| q5 b

/-- Unpack to 8-bit RGB. -/
@[inline] def decode (c : UInt16) : UInt8 × UInt8 × UInt8 :=
  (e5 (c >>> 11), e6 ((c >>> 5) &&& 63), e5 (c &&& 31))

/-- Every RGB565 value survives a round trip through 8-bit RGB. -/
theorem encode_decode (c : UInt16) :
    encode (decode c).1 (decode c).2.1 (decode c).2.2 = c := by
  simp only [encode, decode, q5, q6, e5, e6]; bv_decide

/-- Each channel of `encode` decodes back to within half a step of the input. -/
theorem decode_encode_fields (r g b : UInt8) :
    (encode r g b) >>> 11 = q5 r ∧ ((encode r g b) >>> 5) &&& 63 = q6 g ∧
      (encode r g b) &&& 31 = q5 b := by
  simp only [encode, q5, q6]; bv_decide

end RGB565

namespace Mono

/-- Integer Rec.601 luma, `(77 r + 150 g + 29 b) / 256 ∈ [0, 255]`. -/
@[inline] def luma (r g b : UInt8) : UInt8 :=
  ((77 * r.toUInt32 + 150 * g.toUInt32 + 29 * b.toUInt32) >>> 8).toUInt8

theorem luma_white : luma 255 255 255 = 255 := by decide
theorem luma_black : luma 0 0 0 = 0 := by decide
/-- Luma is a convex combination: it never exceeds the brightest channel. -/
theorem luma_le_max (r g b : UInt8) :
    luma r g b ≤ max r (max g b) := by
  unfold luma; bv_decide

/-- A pixel is lit when its luma reaches `threshold` (default: mid-gray). -/
@[inline] def lit (p : RGBA8) (threshold : UInt8 := 128) : Bool :=
  luma p.r p.g p.b ≥ threshold

end Mono

namespace FrameBuffer

variable {w h : Nat}

/-- Big-endian RGB565 bytes, row-major (`2 * w * h` bytes): ready for SPI DMA.
Alpha is dropped: render onto an opaque background. -/
def toRGB565 (fb : FrameBuffer w h) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (2 * w * h)
  for i in [0:w * h] do
    let c := RGB565.encode fb.data[4 * i]! fb.data[4 * i + 1]! fb.data[4 * i + 2]!
    out := out.push (c >>> 8).toUInt8 |>.push c.toUInt8
  return out

/-- SSD1306 page layout: byte `(y / 8) * w + x`, bit `y % 8` (LSB at the top).
`h` is rounded up to a whole page; padding pixels are dark. -/
def toMonoPages (fb : FrameBuffer w h) (threshold : UInt8 := 128) : ByteArray := Id.run do
  let pages := (h + 7) / 8
  let mut out := ByteArray.emptyWithCapacity (pages * w)
  for page in [0:pages] do
    for x in [0:w] do
      let mut byte : UInt8 := 0
      for bit in [0:8] do
        let y := page * 8 + bit
        if y < h then
          let i := 4 * (y * w + x)
          if Mono.lit ⟨fb.data[i]!, fb.data[i + 1]!, fb.data[i + 2]!, 255⟩ threshold then
            byte := byte ||| ((1 : UInt8) <<< bit.toUInt8)
      out := out.push byte
  return out

/-- Row-major, MSB-first, each row padded to a whole byte (Sharp memory LCD, XBM-like). -/
def toMonoRows (fb : FrameBuffer w h) (threshold : UInt8 := 128) : ByteArray := Id.run do
  let stride := (w + 7) / 8
  let mut out := ByteArray.emptyWithCapacity (stride * h)
  for y in [0:h] do
    for bx in [0:stride] do
      let mut byte : UInt8 := 0
      for bit in [0:8] do
        let x := bx * 8 + bit
        if x < w then
          let i := 4 * (y * w + x)
          if Mono.lit ⟨fb.data[i]!, fb.data[i + 1]!, fb.data[i + 2]!, 255⟩ threshold then
            byte := byte ||| ((0x80 : UInt8) >>> bit.toUInt8)
      out := out.push byte
  return out

/-- Preview: what an RGB565 panel shows, as an opaque RGBA buffer. -/
def ofRGB565 (w h : Nat) (bytes : ByteArray) : FrameBuffer w h :=
  let arr := Array.ofFn (n := w * h * 4) fun i =>
    let p := i.val / 4
    let c := (bytes[2 * p]!.toUInt16 <<< 8) ||| bytes[2 * p + 1]!.toUInt16
    let (r, g, b) := RGB565.decode c
    match i.val % 4 with
    | 0 => r | 1 => g | 2 => b | _ => 255
  ⟨⟨arr⟩, Array.size_ofFn⟩

/-- Preview of a page-packed 1-bit buffer (`on`/`off` colors). -/
def ofMonoPages (w h : Nat) (bytes : ByteArray) (on : RGBA8 := ⟨255, 255, 255, 255⟩)
    (off : RGBA8 := ⟨0, 0, 0, 255⟩) : FrameBuffer w h :=
  let arr := Array.ofFn (n := w * h * 4) fun i =>
    let p := i.val / 4
    let x := p % w; let y := p / w
    let lit := (bytes[(y / 8) * w + x]! >>> (y % 8).toUInt8) &&& 1 == 1
    let c := if lit then on else off
    match i.val % 4 with
    | 0 => c.r | 1 => c.g | 2 => c.b | _ => c.a
  ⟨⟨arr⟩, Array.size_ofFn⟩

end FrameBuffer

end UVL
