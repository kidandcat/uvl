/-!
# Deflate / zlib (pure Lean)

A small, dependency-free DEFLATE encoder (RFC 1951) using LZ77 with hash
chains and the fixed Huffman code, wrapped in a zlib stream (RFC 1950).
Good enough to produce compact PNGs without linking zlib.
-/

namespace UVL.Deflate

structure BitWriter where
  out : ByteArray := ByteArray.emptyWithCapacity 1024
  buf : UInt64 := 0
  nbits : UInt64 := 0

namespace BitWriter

/-- Append the `count` low bits of `v`, LSB first. -/
@[inline] def bits (w : BitWriter) (v : UInt64) (count : UInt64) : BitWriter := Id.run do
  let mut buf := w.buf ||| (v <<< w.nbits)
  let mut n := w.nbits + count
  let mut out := w.out
  while n >= 8 do
    out := out.push (buf &&& 0xFF).toUInt8
    buf := buf >>> 8
    n := n - 8
  return { out, buf, nbits := n }

@[inline] def reverse (code : UInt64) (len : UInt64) : UInt64 := Id.run do
  let mut r : UInt64 := 0
  let mut c := code
  for _ in [0:len.toNat] do
    r := (r <<< 1) ||| (c &&& 1)
    c := c >>> 1
  return r

/-- Append a Huffman code (stored MSB first). -/
@[inline] def huff (w : BitWriter) (code len : UInt64) : BitWriter := w.bits (reverse code len) len

def flush (w : BitWriter) : ByteArray :=
  if w.nbits > 0 then w.out.push (w.buf &&& 0xFF).toUInt8 else w.out

end BitWriter

@[inline] def writeLit (w : BitWriter) (lit : Nat) : BitWriter :=
  let l := lit.toUInt64
  if lit < 144 then w.huff (0x30 + l) 8
  else if lit < 256 then w.huff (0x190 + l - 144) 9
  else if lit < 280 then w.huff (l - 256) 7
  else w.huff (0xC0 + l - 280) 8

def lenBase : Array Nat := #[3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
  35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]
def lenExtra : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
  3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]
def distBase : Array Nat := #[1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
  257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577]
def distExtra : Array Nat := #[0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
  7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]

/-- Index of the last table entry `≤ v`. -/
def findCode (table : Array Nat) (v : Nat) : Nat := Id.run do
  let mut i := 0
  for j in [0:table.size] do
    if table[j]! <= v then i := j
  return i

def writeMatch (w : BitWriter) (len dist : Nat) : BitWriter :=
  let lc := findCode lenBase len
  let w := writeLit w (257 + lc)
  let w := w.bits (len - lenBase[lc]!).toUInt64 lenExtra[lc]!.toUInt64
  let dc := findCode distBase dist
  let w := w.huff dc.toUInt64 5
  w.bits (dist - distBase[dc]!).toUInt64 distExtra[dc]!.toUInt64

def hashBits : Nat := 15
def windowSize : Nat := 32768
def maxChain : Nat := 24
def maxMatch : Nat := 258

@[inline] def hash3 (d : ByteArray) (i : Nat) : Nat :=
  ((d[i]!.toNat <<< 10) ^^^ (d[i+1]!.toNat <<< 5) ^^^ d[i+2]!.toNat) % (1 <<< hashBits)

/-- Raw DEFLATE stream (single final block, fixed Huffman codes). -/
def deflate (d : ByteArray) : ByteArray := Id.run do
  let n := d.size
  let mut w : BitWriter := {}
  w := w.bits 1 1   -- BFINAL
  w := w.bits 1 2   -- BTYPE = 01 (fixed Huffman)
  let mut head : Array Int := Array.replicate (1 <<< hashBits) (-1)
  let mut prev : Array Int := Array.replicate n (-1)
  let mut i := 0
  while i < n do
    let mut bestLen := 0
    let mut bestDist := 0
    if i + 2 < n then
      let hv := hash3 d i
      let mut cand := head[hv]!
      let mut chain := 0
      while cand >= 0 && chain < maxChain && i - cand.toNat <= windowSize do
        let c := cand.toNat
        let limit := Min.min maxMatch (n - i)
        let mut l := 0
        while l < limit && d[c + l]! == d[i + l]! do
          l := l + 1
        if l > bestLen then
          bestLen := l
          bestDist := i - c
        if l >= limit then chain := maxChain
        cand := prev[c]!
        chain := chain + 1
      prev := prev.set! i head[hv]!
      head := head.set! hv i
    if bestLen >= 3 then
      w := writeMatch w bestLen bestDist
      -- insert the skipped positions into the hash chains
      for j in [i + 1:i + bestLen] do
        if j + 2 < n then
          let hv := hash3 d j
          prev := prev.set! j head[hv]!
          head := head.set! hv j
      i := i + bestLen
    else
      w := writeLit w d[i]!.toNat
      i := i + 1
  w := writeLit w 256
  return w.flush

def adler32 (d : ByteArray) : UInt32 := Id.run do
  let mut a : UInt32 := 1
  let mut b : UInt32 := 0
  for x in d do
    a := (a + x.toUInt32) % 65521
    b := (b + a) % 65521
  return (b <<< 16) ||| a

def pushBE32 (out : ByteArray) (v : UInt32) : ByteArray :=
  out.push (v >>> 24).toUInt8 |>.push (v >>> 16).toUInt8 |>.push (v >>> 8).toUInt8 |>.push v.toUInt8

/-- zlib stream: header, deflate data, Adler-32 trailer. -/
def zlib (d : ByteArray) : ByteArray :=
  let hdr := ByteArray.empty.push 0x78 |>.push 0x01
  pushBE32 (hdr ++ deflate d) (adler32 d)

end UVL.Deflate
