import UVL.Output.Image
import UVL.Output.Inflate

/-!
# PNG decoder

Decodes non-interlaced 8-bit PNGs (grayscale, RGB, palette with optional
`tRNS`, grayscale+alpha, RGBA) to straight-alpha RGBA8, which is the layout of
`FrameBuffer` and of sprite textures. Chunk CRCs and the zlib Adler-32 are
checked; ancillary chunks other than `tRNS` are ignored.
-/

namespace UVL.Image

def be32 (d : ByteArray) (i : Nat) : Nat :=
  (d[i]!.toNat <<< 24) ||| (d[i+1]!.toNat <<< 16) ||| (d[i+2]!.toNat <<< 8) ||| d[i+3]!.toNat

/-- Undo the per-row filters in place: `raw` holds `h` rows of `1 + stride`
bytes, `bpp` is bytes per pixel. -/
def unfilter (raw : ByteArray) (stride h bpp : Nat) : Except String ByteArray := do
  let mut out := ByteArray.emptyWithCapacity (stride * h)
  for y in [0:h] do
    let row := y * (stride + 1)
    let f := raw[row]!
    if f > 4 then throw s!"bad filter type {f}"
    for x in [0:stride] do
      let v := raw[row + 1 + x]!
      let a := if x >= bpp then out[y * stride + x - bpp]! else 0
      let b := if y > 0 then out[(y - 1) * stride + x]! else 0
      let pred : UInt8 := match f with
        | 1 => a
        | 2 => b
        | 3 => ((a.toNat + b.toNat) / 2).toUInt8
        | 4 =>
          let c := if x >= bpp && y > 0 then out[(y - 1) * stride + x - bpp]! else 0
          let p : Int := a.toNat + b.toNat - c.toNat
          let pa := (p - a.toNat).natAbs; let pb := (p - b.toNat).natAbs
          let pc := (p - c.toNat).natAbs
          if pa <= pb && pa <= pc then a else if pb <= pc then b else c
        | _ => 0
      out := out.push (v + pred)
  return out

/-- Decode a PNG to `(width, height, rgba)` with straight alpha. -/
def decodePNG (png : ByteArray) : Except String (Nat × Nat × ByteArray) := do
  let sig : ByteArray := ⟨#[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A]⟩
  if png.size < 8 || png.extract 0 8 != sig then throw "not a PNG"
  let mut i := 8
  let mut w := 0
  let mut h := 0
  let mut colorType := 0
  let mut palette := ByteArray.empty
  let mut trns := ByteArray.empty
  let mut idat := ByteArray.empty
  let mut ended := false
  while !ended && i + 12 <= png.size do
    let len := be32 png i
    if i + 12 + len > png.size then throw "truncated chunk"
    let ty := String.fromUTF8! (png.extract (i + 4) (i + 8))
    let body := png.extract (i + 8) (i + 8 + len)
    if crc32 (png.extract (i + 4) (i + 8 + len)) != (be32 png (i + 8 + len)).toUInt32 then
      throw s!"bad CRC in {ty}"
    match ty with
    | "IHDR" =>
      w := be32 body 0; h := be32 body 4
      colorType := body[9]!.toNat
      if body[8]! != 8 then throw s!"unsupported bit depth {body[8]!}"
      if body[12]! != 0 then throw "interlaced PNGs not supported"
    | "PLTE" => palette := body
    | "tRNS" => trns := body
    | "IDAT" => idat := idat ++ body
    | "IEND" => ended := true
    | _ => pure ()
    i := i + 12 + len
  let bpp ← match colorType with
    | 0 => pure 1 | 2 => pure 3 | 3 => pure 1 | 4 => pure 2 | 6 => pure 4
    | c => throw s!"bad color type {c}"
  let raw ← Inflate.zlib idat
  let stride := w * bpp
  if raw.size != (stride + 1) * h then throw s!"bad image data size {raw.size}"
  let px ← unfilter raw stride h bpp
  if colorType == 6 then return (w, h, px)
  let mut out := ByteArray.emptyWithCapacity (w * h * 4)
  for p in [0:w * h] do
    let o := p * bpp
    match colorType with
    | 0 =>
      let g := px[o]!
      let a : UInt8 := if trns.size >= 2 && trns[1]! == g && trns[0]! == 0 then 0 else 255
      out := out.push g |>.push g |>.push g |>.push a
    | 2 =>
      let r := px[o]!; let g := px[o+1]!; let b := px[o+2]!
      let a : UInt8 :=
        if trns.size >= 6 && trns[1]! == r && trns[3]! == g && trns[5]! == b
          && trns[0]! == 0 && trns[2]! == 0 && trns[4]! == 0 then 0 else 255
      out := out.push r |>.push g |>.push b |>.push a
    | 3 =>
      let k := px[o]!.toNat
      if 3 * k + 2 >= palette.size then throw "palette index out of range"
      let a := if k < trns.size then trns[k]! else 255
      out := out.push palette[3*k]! |>.push palette[3*k+1]! |>.push palette[3*k+2]! |>.push a
    | _ =>
      let g := px[o]!
      out := out.push g |>.push g |>.push g |>.push px[o+1]!
  return (w, h, out)

/-- Decode a PNG into a `FrameBuffer`. -/
def decodePNGFrame (png : ByteArray) : Except String ((w h : Nat) × FrameBuffer w h) := do
  let (w, h, px) ← decodePNG png
  if hs : px.size = w * h * 4 then return ⟨w, h, ⟨px, hs⟩⟩
  else throw "decoded size mismatch"

def readPNG (path : System.FilePath) : IO ((w h : Nat) × FrameBuffer w h) := do
  match decodePNGFrame (← IO.FS.readBinFile path) with
  | .ok r => pure r
  | .error e => throw (IO.userError s!"{path}: {e}")

end UVL.Image
