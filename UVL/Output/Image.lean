import UVL.Render.FrameBuffer
import UVL.Output.Deflate

/-!
# Image encoders

Zero-dependency PPM (P6) and PNG (RGBA8) encoders for `FrameBuffer`.
-/

namespace UVL.Image

open Deflate

/-- Binary PPM (drops alpha). -/
def toPPM {w h : Nat} (fb : FrameBuffer w h) : ByteArray := Id.run do
  let mut out := s!"P6\n{w} {h}\n255\n".toUTF8
  for i in [0:w * h] do
    out := out.push fb.data[4 * i]! |>.push fb.data[4 * i + 1]! |>.push fb.data[4 * i + 2]!
  return out

def crcTable : Array UInt32 := Id.run do
  let mut t := Array.emptyWithCapacity 256
  for n in [0:256] do
    let mut c := n.toUInt32
    for _ in [0:8] do
      c := if c &&& 1 == 1 then (0xEDB88320 : UInt32) ^^^ (c >>> 1) else c >>> 1
    t := t.push c
  return t

def crc32 (d : ByteArray) : UInt32 := Id.run do
  let mut c : UInt32 := 0xFFFFFFFF
  for x in d do
    c := crcTable[((c ^^^ x.toUInt32) &&& 0xFF).toNat]! ^^^ (c >>> 8)
  return c ^^^ 0xFFFFFFFF

def chunk (out : ByteArray) (type : String) (body : ByteArray) : ByteArray :=
  let tb := type.toUTF8 ++ body
  pushBE32 (pushBE32 out body.size.toUInt32 ++ tb) (crc32 tb)

@[inline] def absDiff (a : UInt8) : Nat := let v := a.toNat; if v < 128 then v else 256 - v

/-- PNG scanlines with a per-row filter chosen among None/Sub/Up (min-sum heuristic). -/
def filtered {w h : Nat} (fb : FrameBuffer w h) : ByteArray := Id.run do
  let stride := w * 4
  let d := fb.data
  let mut out := ByteArray.emptyWithCapacity ((stride + 1) * h)
  for y in [0:h] do
    let base := y * stride
    let mut sNone := 0
    let mut sSub := 0
    let mut sUp := 0
    for i in [0:stride] do
      let v := d[base + i]!
      let left := if i >= 4 then d[base + i - 4]! else 0
      let up := if y > 0 then d[base + i - stride]! else 0
      sNone := sNone + absDiff v
      sSub := sSub + absDiff (v - left)
      sUp := sUp + absDiff (v - up)
    let filt : UInt8 := if sNone <= sSub && sNone <= sUp then 0 else if sSub <= sUp then 1 else 2
    out := out.push filt
    for i in [0:stride] do
      let v := d[base + i]!
      let b := match filt with
        | 1 => v - (if i >= 4 then d[base + i - 4]! else 0)
        | 2 => v - (if y > 0 then d[base + i - stride]! else 0)
        | _ => v
      out := out.push b
  return out

def toPNG {w h : Nat} (fb : FrameBuffer w h) : ByteArray :=
  let sig : ByteArray := ⟨#[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]⟩
  let ihdr := pushBE32 (pushBE32 ByteArray.empty w.toUInt32) h.toUInt32
    |>.push 8 |>.push 6 |>.push 0 |>.push 0 |>.push 0
  let out := chunk sig "IHDR" ihdr
  let out := chunk out "IDAT" (zlib (filtered fb))
  chunk out "IEND" ByteArray.empty

def writePNG {w h : Nat} (path : System.FilePath) (fb : FrameBuffer w h) : IO Unit :=
  IO.FS.writeBinFile path (toPNG fb)

def writePPM {w h : Nat} (path : System.FilePath) (fb : FrameBuffer w h) : IO Unit :=
  IO.FS.writeBinFile path (toPPM fb)

end UVL.Image
