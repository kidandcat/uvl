import UVL.Render.Path
import UVL.Render.MSDF

/-!
# TrueType fonts

A reader for TrueType (`glyf`) fonts in pure Lean: the table directory,
`head`, `hhea`, `maxp`, `hmtx`, `cmap` (formats 4 and 12), `loca`/`glyf` with
simple and composite glyphs, and pair kerning from the `kern` table.

Glyph outlines become `Path`s of quadratic Bézier curves in font units (y up),
so text is drawn by the same path filler as any other vector shape, on the CPU
and on the GPU.
-/

namespace UVL.Text

/-! ### Big-endian reading -/

@[inline] def u8 (d : ByteArray) (o : Nat) : Nat := (d.get! o).toNat
@[inline] def u16 (d : ByteArray) (o : Nat) : Nat := u8 d o * 256 + u8 d (o + 1)
@[inline] def i16 (d : ByteArray) (o : Nat) : Int :=
  let v := u16 d o
  if v ≥ 32768 then (v : Int) - 65536 else v
@[inline] def u32 (d : ByteArray) (o : Nat) : Nat := u16 d o * 65536 + u16 d (o + 2)

/-- `F2DOT14` fixed point (composite glyph scales). -/
@[inline] def f2dot14 (d : ByteArray) (o : Nat) : Float := Float.ofInt (i16 d o) / 16384.0

/-- A glyph outline in font units, with its horizontal metrics. -/
structure Glyph where
  path : Path := {}
  advance : Float := 0
deriving Inhabited

structure Font where
  data : ByteArray
  unitsPerEm : Float
  ascender : Float
  descender : Float
  lineGap : Float
  numGlyphs : Nat
  /-- `(codepoint, glyph)` pairs sorted by codepoint. -/
  cmap : Array (Nat × Nat)
  /-- `(left * 65536 + right, adjustment)` sorted by key. -/
  kerning : Array (Nat × Float)
  glyphs : Array Glyph
  /-- The font's MSDF atlas (texels computed glyph by glyph on first use). -/
  atlas : MSDF.Atlas
deriving Inhabited

/-- Sort pairs by key (bottom-up merge sort). Written out because the compiled
specialization of `Array.qsort` lives in the `Lean` package, which the
WebAssembly build does not link. -/
def sortByKey {α : Type} [Inhabited α] (a : Array (Nat × α)) : Array (Nat × α) := Id.run do
  let n := a.size
  let mut src := a
  let mut width := 1
  while width < n do
    let mut dst : Array (Nat × α) := Array.mkEmpty n
    let mut lo := 0
    while lo < n do
      let mid := Min.min (lo + width) n
      let hi := Min.min (lo + 2 * width) n
      let mut i := lo
      let mut j := mid
      while i < mid || j < hi do
        if j >= hi || (i < mid && src[i]!.1 <= src[j]!.1) then
          dst := dst.push src[i]!; i := i + 1
        else
          dst := dst.push src[j]!; j := j + 1
      lo := hi
    src := dst
    width := 2 * width
  return src

/-- Offset of a table, by its 4-character tag. -/
def tableOffset (d : ByteArray) (tag : String) : Option Nat := Id.run do
  let n := u16 d 4
  let t := tag.toUTF8
  for i in [0:n] do
    let r := 12 + 16 * i
    if t.size == 4 && u8 d r == t[0]!.toNat && u8 d (r + 1) == t[1]!.toNat
        && u8 d (r + 2) == t[2]!.toNat && u8 d (r + 3) == t[3]!.toNat then
      return some (u32 d (r + 8))
  return none

/-- Character map: format 4 (BMP) or 12 (full Unicode) subtable. -/
def readCmap (d : ByteArray) (cmap : Nat) : Array (Nat × Nat) := Id.run do
  let n := u16 d (cmap + 2)
  -- prefer a full-Unicode format 12 table, then a BMP one
  let mut best : Option Nat := none
  let mut bestRank := 0
  for i in [0:n] do
    let r := cmap + 4 + 8 * i
    let pid := u16 d r
    let eid := u16 d (r + 2)
    let off := cmap + u32 d (r + 4)
    let fmt := u16 d off
    let rank :=
      if fmt == 12 && (pid == 0 || (pid == 3 && eid == 10)) then 3
      else if fmt == 4 && (pid == 0 || (pid == 3 && eid == 1)) then 2
      else 0
    if rank > bestRank then
      best := some off
      bestRank := rank
  let some off := best | return #[]
  let mut out : Array (Nat × Nat) := #[]
  if u16 d off == 12 then
    let groups := u32 d (off + 12)
    for g in [0:groups] do
      let r := off + 16 + 12 * g
      let start := u32 d r
      let stop := u32 d (r + 4)
      let gid := u32 d (r + 8)
      for c in [start:stop + 1] do
        out := out.push (c, gid + (c - start))
  else
    let segX2 := u16 d (off + 6)
    let ends := off + 14
    let starts := ends + segX2 + 2
    let deltas := starts + segX2
    let ranges := deltas + segX2
    for s in [0:segX2 / 2] do
      let stop := u16 d (ends + 2 * s)
      let start := u16 d (starts + 2 * s)
      let delta := u16 d (deltas + 2 * s)
      let ro := u16 d (ranges + 2 * s)
      if start > stop || start == 0xFFFF then continue
      for c in [start:stop + 1] do
        let g :=
          if ro == 0 then (c + delta) % 65536
          else
            let gi := u16 d (ranges + 2 * s + ro + 2 * (c - start))
            if gi == 0 then 0 else (gi + delta) % 65536
        if g != 0 then out := out.push (c, g)
  return sortByKey out

/-- Pairs of the first format-0 subtable of a version-0 `kern` table. -/
def readKern (d : ByteArray) (unitsPerEm : Float) : Option Nat → Array (Nat × Float)
  | none => #[]
  | some k => Id.run do
    if u16 d k != 0 || u16 d (k + 2) == 0 then return #[]
    let sub := k + 4
    if u16 d (sub + 4) / 256 != 0 then return #[] -- format 0 only
    let n := u16 d (sub + 6)
    let mut out := #[]
    for i in [0:n] do
      let r := sub + 14 + 6 * i
      out := out.push (u16 d r * 65536 + u16 d (r + 2), Float.ofInt (i16 d (r + 4)) / unitsPerEm)
    return sortByKey out

/-- Quadratic contour from TrueType points (on/off curve, implied midpoints). -/
def contourPath (p : Path) (pts : Array (Float × Float × Bool)) : Path := Id.run do
  if pts.isEmpty then return p
  let n := pts.size
  let mid (a b : Float × Float × Bool) : Vec2 := ⟨(a.1 + b.1) / 2, (a.2.1 + b.2.1) / 2⟩
  let pt (a : Float × Float × Bool) : Vec2 := ⟨a.1, a.2.1⟩
  -- start on an on-curve point (or the midpoint of two off-curve points)
  let first := pts[0]!
  let lastP := pts[n - 1]!
  let start : Vec2 := if first.2.2 then pt first else if lastP.2.2 then pt lastP else mid lastP first
  let mut path := p.moveTo start.x start.y
  let mut ctrl : Option Vec2 := none
  for k in [0:n] do
    let q := pts[(k + (if first.2.2 then 1 else 0)) % n]!
    if q.2.2 then
      match ctrl with
      | some c => path := path.quadTo c.x c.y q.1 q.2.1
      | none => path := path.lineTo q.1 q.2.1
      ctrl := none
    else
      match ctrl with
      | some c =>
        let m : Vec2 := ⟨(c.x + q.1) / 2, (c.y + q.2.1) / 2⟩
        path := path.quadTo c.x c.y m.x m.y
      | none => pure ()
      ctrl := some (pt q)
  if let some c := ctrl then path := path.quadTo c.x c.y start.x start.y
  return path.close

/-- Outline of glyph `g` through the affine map `m` (composites recurse). -/
partial def outline (d : ByteArray) (glyf loca : Nat) (longLoca : Bool) (numGlyphs : Nat)
    (g : Nat) (m : Affine) (depth : Nat := 0) (acc : Path := {}) : Path := Id.run do
  if g ≥ numGlyphs || depth > 8 then return acc
  let (o0, o1) :=
    if longLoca then (u32 d (loca + 4 * g), u32 d (loca + 4 * g + 4))
    else (2 * u16 d (loca + 2 * g), 2 * u16 d (loca + 2 * g + 2))
  if o1 ≤ o0 then return acc
  let o := glyf + o0
  let nc := i16 d o
  if nc ≥ 0 then
    -- simple glyph
    let nc := nc.toNat
    let ends := (List.range nc).map fun i => u16 d (o + 10 + 2 * i)
    let npts := match ends.getLast? with | some e => e + 1 | none => 0
    let ilen := u16 d (o + 10 + 2 * nc)
    let mut p := o + 12 + 2 * nc + ilen
    let mut flags : Array Nat := #[]
    while flags.size < npts do
      let f := u8 d p
      p := p + 1
      flags := flags.push f
      if f &&& 8 != 0 then
        let r := u8 d p
        p := p + 1
        for _ in [0:r] do flags := flags.push f
    let mut xs : Array Int := #[]
    let mut v : Int := 0
    for f in flags do
      if f &&& 2 != 0 then
        let dx := u8 d p
        p := p + 1
        v := v + (if f &&& 16 != 0 then (dx : Int) else -(dx : Int))
      else if f &&& 16 == 0 then
        v := v + i16 d p
        p := p + 2
      xs := xs.push v
    let mut ys : Array Int := #[]
    v := 0
    for f in flags do
      if f &&& 4 != 0 then
        let dy := u8 d p
        p := p + 1
        v := v + (if f &&& 32 != 0 then (dy : Int) else -(dy : Int))
      else if f &&& 32 == 0 then
        v := v + i16 d p
        p := p + 2
      ys := ys.push v
    let mut path := acc
    let mut s := 0
    for e in ends do
      let pts := (List.range (e + 1 - s)).toArray.map fun k =>
        let q := m.apply ⟨Float.ofInt xs[s + k]!, Float.ofInt ys[s + k]!⟩
        (q.x, q.y, flags[s + k]! &&& 1 != 0)
      path := contourPath path pts
      s := e + 1
    return path
  else
    -- composite glyph
    let mut p := o + 10
    let mut path := acc
    let mut more := true
    while more do
      let flags := u16 d p
      let sub := u16 d (p + 2)
      p := p + 4
      let words := flags &&& 1 != 0
      let (a1, a2) :=
        if words then (i16 d p, i16 d (p + 2)) else
          let b1 := u8 d p; let b2 := u8 d (p + 1)
          ((if b1 ≥ 128 then (b1 : Int) - 256 else b1), (if b2 ≥ 128 then (b2 : Int) - 256 else b2))
      p := p + (if words then 4 else 2)
      let mut t : Affine := { e := Float.ofInt a1, f := Float.ofInt a2 }
      if flags &&& 8 != 0 then
        let s := f2dot14 d p
        t := { t with a := s, d := s }
        p := p + 2
      else if flags &&& 64 != 0 then
        t := { t with a := f2dot14 d p, d := f2dot14 d (p + 2) }
        p := p + 4
      else if flags &&& 128 != 0 then
        t := { t with a := f2dot14 d p, b := f2dot14 d (p + 2), c := f2dot14 d (p + 4),
                      d := f2dot14 d (p + 6) }
        p := p + 8
      -- point-matching placement (ARGS_ARE_XY_VALUES unset) is not supported
      if flags &&& 2 == 0 then t := { t with e := 0, f := 0 }
      path := outline d glyf loca longLoca numGlyphs sub (m.compose t) (depth + 1) path
      more := flags &&& 32 != 0
    return path

/-- Parse a TrueType font. Outlines are converted once, scaled to the em
square (1 unit = 1 em) with y pointing down. `atlasId` identifies the font's
MSDF atlas (GPU hosts key uploaded glyphs by it): give each loaded font its own
(the bundled font uses 0). -/
def Font.load (d : ByteArray) (atlasId : Nat := 0) : Except String Font := do
  let some head := tableOffset d "head" | throw "no head table"
  let some hhea := tableOffset d "hhea" | throw "no hhea table"
  let some maxp := tableOffset d "maxp" | throw "no maxp table"
  let some hmtx := tableOffset d "hmtx" | throw "no hmtx table"
  let some cmap := tableOffset d "cmap" | throw "no cmap table"
  let some loca := tableOffset d "loca" | throw "no loca table (CFF fonts are not supported)"
  let some glyf := tableOffset d "glyf" | throw "no glyf table (CFF fonts are not supported)"
  let upem := (u16 d (head + 18)).toFloat
  if upem == 0 then throw "unitsPerEm is 0"
  let longLoca := i16 d (head + 50) == 1
  let numGlyphs := u16 d (maxp + 4)
  let numH := u16 d (hhea + 34)
  let em : Affine := { a := 1 / upem, d := -1 / upem }
  let glyphs := (Array.range numGlyphs).map fun g =>
    let adv := u16 d (hmtx + 4 * (Min.min g (numH - 1)))
    { path := outline d glyf loca longLoca numGlyphs g em, advance := adv.toFloat / upem }
  return {
    data := d, unitsPerEm := upem
    ascender := Float.ofInt (i16 d (hhea + 4)) / upem
    descender := Float.ofInt (i16 d (hhea + 6)) / upem
    lineGap := Float.ofInt (i16 d (hhea + 8)) / upem
    numGlyphs, cmap := readCmap d cmap
    kerning := readKern d upem (tableOffset d "kern")
    glyphs, atlas := MSDF.Atlas.ofOutlines atlasId (glyphs.map (·.path)) }

/-- Binary search in an array sorted by key. -/
def findKey {α : Type} (arr : Array (Nat × α)) (k : Nat) : Option α := Id.run do
  let mut lo := 0
  let mut hi := arr.size
  while lo < hi do
    let mid := (lo + hi) / 2
    let some (key, v) := arr[mid]? | return none
    if key == k then return some v
    if key < k then lo := mid + 1 else hi := mid
  return none

namespace Font

/-- Glyph index of a character (0, the `.notdef` glyph, when missing). -/
def glyphIndex (f : Font) (c : Char) : Nat := (findKey f.cmap c.toNat).getD 0

/-- Kerning between two glyphs, in ems. -/
def kern (f : Font) (l r : Nat) : Float :=
  if f.kerning.isEmpty then 0 else (findKey f.kerning (l * 65536 + r)).getD 0

def glyph (f : Font) (g : Nat) : Glyph := f.glyphs[g]?.getD {}

/-- Line height (ascender − descender + line gap), in ems. -/
def lineHeight (f : Font) : Float := f.ascender - f.descender + f.lineGap

end Font

end UVL.Text
