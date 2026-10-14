import UVL.Text.TrueType
import UVL.Text.UVLSansData
import UVL.Render.RenderOp

/-!
# Text layout with TrueType fonts

Shaping (character map, advances, pair kerning), measuring, greedy line
wrapping, and lowering to render ops.

Glyph outlines are emitted as ordinary path fills, already scaled and placed in
device space, one path per glyph. Everything downstream (the CPU rasterizer,
damage tracking, tiles and the GPU path kernels) therefore draws TrueType text
with no special support.
-/

namespace UVL.Text

/-! ### Base64 -/

private def b64Value (c : UInt8) : Option Nat :=
  if c ≥ 65 && c ≤ 90 then some (c.toNat - 65)
  else if c ≥ 97 && c ≤ 122 then some (c.toNat - 71)
  else if c ≥ 48 && c ≤ 57 then some (c.toNat + 4)
  else if c == 43 then some 62
  else if c == 47 then some 63
  else none

/-- Decode base64, skipping characters outside the alphabet (padding,
whitespace). -/
def base64Decode (s : String) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (s.utf8ByteSize * 3 / 4)
  let mut acc := 0
  let mut bits := 0
  for c in s.toUTF8 do
    if let some v := b64Value c then
      acc := (acc * 64 + v) % 16777216
      bits := bits + 6
      if bits ≥ 8 then
        bits := bits - 8
        out := out.push (acc / 2 ^ bits % 256).toUInt8
  return out

/-- The bundled font: UVL Sans, a Latin-1 subset of Liberation Sans Regular
(SIL Open Font License, see `assets/fonts/OFL.txt`).

It is a function so that the font is decoded on first use, not when the module
is initialized: programs that never draw TrueType text (the bare-metal targets)
pay nothing for it. -/
def uvlSans (_ : Unit := ()) : Font :=
  match Font.load (base64Decode uvlSansBase64) with
  | .ok f => f
  | .error _ => default

/-! ### Shaping -/

/-- A positioned glyph: index and pen position, in ems. -/
structure PlacedGlyph where
  glyph : Nat
  x : Float
deriving Inhabited, Repr

/-- Glyphs of a single line with their pen positions, and the line's advance
width, in ems. -/
def shape (f : Font) (s : String) : Array PlacedGlyph × Float := Id.run do
  let mut out : Array PlacedGlyph := #[]
  let mut x := 0.0
  let mut prev : Option Nat := none
  for c in s.toList do
    let g := f.glyphIndex c
    if let some p := prev then x := x + f.kern p g
    out := out.push { glyph := g, x }
    x := x + (f.glyph g).advance
    prev := some g
  return (out, x)

/-- Width of a single line in pixels at `size` pixels per em. -/
def measure (f : Font) (s : String) (size : Float) : Float := (shape f s).2 * size

/-- Split on `'\n'`, then wrap each paragraph greedily at spaces so that no
line is wider than `maxWidth` pixels (a single over-long word stays on its own
line). -/
def wrap (f : Font) (s : String) (size maxWidth : Float) : Array String := Id.run do
  let mut lines : Array String := #[]
  for para in s.splitOn "\n" do
    let mut cur := ""
    for word in para.splitOn " " do
      let cand := if cur.isEmpty then word else cur ++ " " ++ word
      if cur.isEmpty || measure f cand size ≤ maxWidth then
        cur := cand
      else
        lines := lines.push cur
        cur := word
    lines := lines.push cur
  return lines

/-! ### Lowering -/

private def place (sx ox oy : Float) (p : Vec2) : Vec2 := ⟨p.x * sx + ox, p.y * sx + oy⟩

/-- Append glyph `g`'s outline, scaled by `size` and translated to `(ox, oy)`
(the pen position on the baseline), to `acc`. -/
def appendGlyph (acc : Path) (gp : Path) (size ox oy : Float) : Path := Id.run do
  let mut cmds := acc.cmds
  for c in gp.cmds do
    cmds := cmds.push <| match c with
      | .moveTo p => .moveTo (place size ox oy p)
      | .lineTo p => .lineTo (place size ox oy p)
      | .quadTo a p => .quadTo (place size ox oy a) (place size ox oy p)
      | .cubicTo a b p => .cubicTo (place size ox oy a) (place size ox oy b) (place size ox oy p)
      | .close => .close
  return ⟨cmds⟩

/-- Render ops for one line of text whose baseline starts at `(x, baseline)`:
one path fill per visible glyph. Separate fills keep every GPU primitive small
(its bands only carry that glyph's edges) and let damage tracking repaint only
the glyphs that changed. -/
def lineOps (f : Font) (s : String) (size : Float) (color : Color) (x baseline : Float) :
    Array RenderOp :=
  (shape f s).1.foldl (init := #[]) fun ops pg =>
    let gp := (f.glyph pg.glyph).path
    if gp.cmds.isEmpty then ops
    else ops.push (.fill (.path (appendGlyph {} gp size (x + pg.x * size) baseline)) color)

/-- Render ops for lines of text in a box whose top-left corner is `origin`.
Baselines are snapped to whole pixels so that stems stay crisp. -/
def linesOps (f : Font) (lines : Array String) (size : Float) (color : Color)
    (origin : Vec2) : Array RenderOp := Id.run do
  let lh := f.lineHeight * size
  let mut ops := #[]
  for i in [0:lines.size] do
    let baseline := (origin.y + f.ascender * size + i.toFloat * lh).round
    ops := ops ++ lineOps f lines[i]! size color origin.x baseline
  return ops

/-- MSDF version of `linesOps`: one `glyphs` op per line, drawn from the font's
atlas. Cheaper than outlines for large amounts of text,
especially on the GPU, at the cost of slightly rounder fine details. -/
def linesOpsMSDF (f : Font) (lines : Array String) (size : Float)
    (paint : Paint) (origin : Vec2) : Array RenderOp := Id.run do
  let lh := f.lineHeight * size
  let mut ops := #[]
  for i in [0:lines.size] do
    let baseline := (origin.y + f.ascender * size + i.toFloat * lh).round
    let quads := (shape f lines[i]!).1.filterMap fun pg =>
      if (f.glyph pg.glyph).path.cmds.isEmpty then none
      else some { glyph := pg.glyph, x := origin.x + pg.x * size, y := baseline, size }
    if !quads.isEmpty then ops := ops.push (.glyphs f.atlas quads paint)
  return ops

/-- Size in whole pixels of a block of lines. -/
def linesSize (f : Font) (lines : Array String) (size : Float) : Nat × Nat :=
  let w := lines.foldl (fun m l => Max.max m (measure f l size)) 0
  (w.ceil.toUInt64.toNat, (lines.size.toFloat * f.lineHeight * size).ceil.toUInt64.toNat)

end UVL.Text
