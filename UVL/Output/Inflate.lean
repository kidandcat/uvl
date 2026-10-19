import UVL.Output.Deflate

/-!
# Inflate (pure Lean)

A DEFLATE decoder (RFC 1951) for stored, fixed-Huffman and dynamic-Huffman
blocks, plus the zlib wrapper (RFC 1950). Canonical Huffman codes are decoded
bit by bit from per-length counts (as in zlib's `puff.c`): simple and small,
fast enough for loading assets at startup.
-/

namespace UVL.Inflate

structure Reader where
  data : ByteArray
  /-- Bit position. -/
  pos : Nat := 0

namespace Reader

@[inline] def bit (r : Reader) : Except String (Nat × Reader) :=
  let i := r.pos / 8
  if h : i < r.data.size then
    .ok ((r.data[i].toNat >>> (r.pos % 8)) % 2, { r with pos := r.pos + 1 })
  else .error "unexpected end of deflate stream"

/-- `n` bits, LSB first. -/
def bits (r : Reader) (n : Nat) : Except String (Nat × Reader) := do
  let mut v := 0
  let mut r := r
  for i in [0:n] do
    let (b, r') ← r.bit
    v := v ||| (b <<< i); r := r'
  return (v, r)

end Reader

/-- A canonical Huffman code: number of codes of each length (1–15) and the
symbols ordered by (length, symbol). -/
structure Huffman where
  counts : Array Nat
  symbols : Array Nat

namespace Huffman

def build (lengths : Array Nat) : Huffman := Id.run do
  let mut counts := Array.replicate 16 0
  for l in lengths do
    counts := counts.modify l (· + 1)
  counts := counts.set! 0 0
  let mut offs := Array.replicate 16 0
  for l in [1:15] do
    offs := offs.set! (l + 1) (offs[l]! + counts[l]!)
  let mut symbols := Array.replicate lengths.size 0
  for s in [0:lengths.size] do
    let l := lengths[s]!
    if l != 0 then
      symbols := symbols.set! offs[l]! s
      offs := offs.modify l (· + 1)
  return { counts, symbols }

/-- Decode one symbol, reading the code MSB first. -/
def decode (h : Huffman) (r : Reader) : Except String (Nat × Reader) := do
  let mut code := 0
  let mut first := 0
  let mut index := 0
  let mut r := r
  for len in [1:16] do
    let (b, r') ← r.bit
    r := r'
    code := code ||| b
    let count := h.counts[len]!
    if code < first + count then
      return (h.symbols[index + (code - first)]!, r)
    index := index + count
    first := (first + count) <<< 1
    code := code <<< 1
  throw "invalid Huffman code"

def fixedLit : Huffman := build <| Id.run do
  let mut l := Array.emptyWithCapacity 288
  for s in [0:288] do
    l := l.push (if s < 144 then 8 else if s < 256 then 9 else if s < 280 then 7 else 8)
  return l

def fixedDist : Huffman := build (Array.replicate 30 5)

end Huffman

/-- Order in which code-length code lengths are stored in a dynamic block header. -/
def clOrder : Array Nat := #[16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]

/-- Read the literal/length and distance codes of a dynamic block. -/
def dynamicCodes (r : Reader) : Except String (Huffman × Huffman × Reader) := do
  let (hlit, r) ← r.bits 5
  let (hdist, r) ← r.bits 5
  let (hclen, r) ← r.bits 4
  let nlit := hlit + 257
  let ndist := hdist + 1
  if nlit > 286 || ndist > 30 then throw "bad dynamic block counts"
  let mut r := r
  let mut cl := Array.replicate 19 0
  for i in [0:hclen + 4] do
    let (v, r') ← r.bits 3
    r := r'; cl := cl.set! clOrder[i]! v
  let clCode := Huffman.build cl
  let mut lengths : Array Nat := Array.emptyWithCapacity (nlit + ndist)
  while lengths.size < nlit + ndist do
    let (sym, r') ← clCode.decode r
    r := r'
    if sym < 16 then lengths := lengths.push sym
    else
      let (prev, extra, base) := match sym with
        | 16 => (lengths.back?.getD 0, 2, 3)
        | 17 => (0, 3, 3)
        | _ => (0, 7, 11)
      if sym == 16 && lengths.isEmpty then throw "repeat with no previous length"
      let (e, r') ← r.bits extra
      r := r'
      for _ in [0:base + e] do
        lengths := lengths.push prev
  if lengths.size != nlit + ndist then throw "code lengths overflow"
  return (Huffman.build (lengths.extract 0 nlit), Huffman.build (lengths.extract nlit (nlit + ndist)), r)

/-- Decode the symbols of one Huffman-coded block, appending to `out`. -/
partial def codes (lit dist : Huffman) (r : Reader) (out : ByteArray) :
    Except String (Reader × ByteArray) := do
  let (sym, r) ← lit.decode r
  if sym < 256 then codes lit dist r (out.push sym.toUInt8)
  else if sym == 256 then return (r, out)
  else
    let lc := sym - 257
    if lc ≥ 29 then throw "bad length symbol"
    let (e, r) ← r.bits Deflate.lenExtra[lc]!
    let len := Deflate.lenBase[lc]! + e
    let (dc, r) ← dist.decode r
    if dc ≥ 30 then throw "bad distance symbol"
    let (e, r) ← r.bits Deflate.distExtra[dc]!
    let d := Deflate.distBase[dc]! + e
    if d > out.size then throw "distance too far back"
    let mut out := out
    for _ in [0:len] do
      out := out.push out[out.size - d]!
    codes lit dist r out

/-- Raw DEFLATE stream → bytes. Returns the reader positioned after the final block. -/
partial def raw (r : Reader) (out : ByteArray := ByteArray.empty) :
    Except String (ByteArray × Reader) := do
  let (final, r) ← r.bit
  let (ty, r) ← r.bits 2
  let (r, out) ← match ty with
    | 0 =>
      let byte := (r.pos + 7) / 8
      if byte + 4 > r.data.size then throw "truncated stored block"
      let len := r.data[byte]!.toNat + 256 * r.data[byte + 1]!.toNat
      let nlen := r.data[byte + 2]!.toNat + 256 * r.data[byte + 3]!.toNat
      if len + nlen != 0xFFFF then throw "stored block length mismatch"
      if byte + 4 + len > r.data.size then throw "truncated stored block"
      pure ({ r with pos := (byte + 4 + len) * 8 },
        r.data.copySlice (byte + 4) out out.size len)
    | 1 => codes Huffman.fixedLit Huffman.fixedDist r out
    | 2 => do
      let (lit, dist, r) ← dynamicCodes r
      codes lit dist r out
    | _ => throw "invalid deflate block type"
  if final == 1 then return (out, r) else raw r out

/-- zlib stream → bytes (header and Adler-32 checked). -/
def zlib (d : ByteArray) : Except String ByteArray := do
  if d.size < 6 then throw "zlib stream too short"
  let cmf := d[0]!.toNat; let flg := d[1]!.toNat
  if cmf % 16 != 8 || (cmf * 256 + flg) % 31 != 0 then throw "bad zlib header"
  if flg &&& 0x20 != 0 then throw "zlib preset dictionary not supported"
  let (out, r) ← raw { data := d, pos := 16 }
  let i := (r.pos + 7) / 8
  if i + 4 > d.size then throw "missing Adler-32"
  let sum := (d[i]!.toUInt32 <<< 24) ||| (d[i+1]!.toUInt32 <<< 16) |||
    (d[i+2]!.toUInt32 <<< 8) ||| d[i+3]!.toUInt32
  if sum != Deflate.adler32 out then throw "Adler-32 mismatch"
  return out

end UVL.Inflate
