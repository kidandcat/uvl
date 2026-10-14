import UniversalViz

/-!
Minimal PNG reader used by the golden tests: RGBA8, non-interlaced, zlib
streams made of stored or fixed-Huffman blocks (what our encoder emits), and
row filters None/Sub/Up/Average/Paeth.
-/

namespace Tests.Png

structure BitReader where
  data : ByteArray
  pos : Nat := 0     -- bit position

namespace BitReader
def bit (r : BitReader) : Nat × BitReader :=
  let b := (r.data[r.pos / 8]!.toNat >>> (r.pos % 8)) % 2
  (b, { r with pos := r.pos + 1 })
def bits (r : BitReader) (n : Nat) : Nat × BitReader := Id.run do
  let mut v := 0
  let mut r := r
  for i in [0:n] do
    let (b, r') := r.bit
    v := v ||| (b <<< i); r := r'
  return (v, r)
/-- Read a Huffman code MSB-first, one bit at a time. -/
def code (r : BitReader) (n : Nat) (acc : Nat) : Nat × BitReader := Id.run do
  let mut v := acc
  let mut r := r
  for _ in [0:n] do
    let (b, r') := r.bit
    v := (v <<< 1) ||| b; r := r'
  return (v, r)
end BitReader

def decodeLit (r : BitReader) : Nat × BitReader :=
  let (c, r) := r.code 7 0
  if c <= 23 then (256 + c, r) else
  let (c, r) := r.code 1 c
  if 48 <= c && c <= 191 then (c - 48, r)
  else if 192 <= c && c <= 199 then (280 + c - 192, r)
  else
    let (c, r) := r.code 1 c
    (144 + c - 400, r)

partial def inflate (d : ByteArray) : Except String ByteArray := do
  let mut r : BitReader := { data := d, pos := 16 }   -- skip zlib header
  let mut out := ByteArray.empty
  let mut final := false
  while !final do
    let (bf, r1) := r.bit; let (bt, r2) := r1.bits 2; r := r2
    final := bf == 1
    if bt == 0 then
      let byte := (r.pos + 7) / 8
      let len := d[byte]!.toNat + 256 * d[byte + 1]!.toNat
      out := out ++ d.extract (byte + 4) (byte + 4 + len)
      r := { r with pos := (byte + 4 + len) * 8 }
    else if bt == 1 then
      let mut done := false
      while !done do
        let (sym, r1) := decodeLit r; r := r1
        if sym < 256 then out := out.push sym.toUInt8
        else if sym == 256 then done := true
        else
          let lc := sym - 257
          let (e, r1) := r.bits UViz.Deflate.lenExtra[lc]!; r := r1
          let len := UViz.Deflate.lenBase[lc]! + e
          let (dc, r1) := r.code 5 0; r := r1
          let (e, r1) := r.bits UViz.Deflate.distExtra[dc]!; r := r1
          let dist := UViz.Deflate.distBase[dc]! + e
          for _ in [0:len] do
            out := out.push out[out.size - dist]!
    else throw "unsupported deflate block type"
  return out

def be32 (d : ByteArray) (i : Nat) : Nat :=
  (d[i]!.toNat <<< 24) ||| (d[i+1]!.toNat <<< 16) ||| (d[i+2]!.toNat <<< 8) ||| d[i+3]!.toNat

/-- Decode to `(width, height, rgba)`. -/
def decode (png : ByteArray) : Except String (Nat × Nat × ByteArray) := do
  if png.size < 8 then throw "too short"
  let mut i := 8
  let mut w := 0
  let mut h := 0
  let mut idat := ByteArray.empty
  while i + 8 <= png.size do
    let len := be32 png i
    let ty := String.fromUTF8! (png.extract (i + 4) (i + 8))
    let body := png.extract (i + 8) (i + 8 + len)
    if UViz.Image.crc32 (png.extract (i + 4) (i + 8 + len)) != (be32 png (i + 8 + len)).toUInt32 then
      throw s!"bad CRC in {ty}"
    if ty == "IHDR" then
      w := be32 body 0; h := be32 body 4
      if body[8]! != 8 || body[9]! != 6 then throw "only RGBA8 supported"
    else if ty == "IDAT" then idat := idat ++ body
    i := i + 12 + len
  let raw ← inflate idat
  let stride := w * 4
  if raw.size != (stride + 1) * h then throw s!"bad data size {raw.size}"
  let mut out := ByteArray.emptyWithCapacity (stride * h)
  for y in [0:h] do
    let f := raw[y * (stride + 1)]!
    for x in [0:stride] do
      let v := raw[y * (stride + 1) + 1 + x]!
      let a := if x >= 4 then out[y * stride + x - 4]! else 0
      let b := if y > 0 then out[(y - 1) * stride + x]! else 0
      let c := if x >= 4 && y > 0 then out[(y - 1) * stride + x - 4]! else 0
      let pred : UInt8 := match f with
        | 1 => a
        | 2 => b
        | 3 => ((a.toNat + b.toNat) / 2).toUInt8
        | 4 =>
          let p : Int := a.toNat + b.toNat - c.toNat
          let pa := (p - a.toNat).natAbs; let pb := (p - b.toNat).natAbs; let pc := (p - c.toNat).natAbs
          if pa <= pb && pa <= pc then a else if pb <= pc then b else c
        | _ => 0
      out := out.push (v + pred)
  return (w, h, out)

end Tests.Png
