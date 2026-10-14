import UVL.GPU.Reference
import Examples.Scenes

/-!
TrueType checks: the bundled font's tables, character map and kerning, line
wrapping, and text drawn through the GPU program matching the CPU rasterizer.
-/

namespace Tests.Text
open UVL UVL.Text

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  [{if cond then "ok" else "FAIL"}] {name}"
  return cond

def run : IO Bool := do
  let f := uvlSans ()
  let mut ok ← check s!"UVL Sans loads: {f.numGlyphs} glyphs, {f.cmap.size} code points, {f.kerning.size} kerning pairs"
    (f.numGlyphs == 214 && f.unitsPerEm == 2048 && f.cmap.size > 190 && f.kerning.size > 50)
  let a := f.glyphIndex 'A'
  let v := f.glyphIndex 'V'
  ok := (← check "cmap: 'A', 'V', 'ñ' mapped; unmapped → .notdef"
    (a != 0 && v != 0 && f.glyphIndex 'ñ' != 0 && f.glyphIndex '中' == 0)) && ok
  ok := (← check s!"metrics: ascender {f.ascender}, descender {f.descender}, advance(A) {(f.glyph a).advance}"
    ((f.ascender - 0.905).abs < 0.001 && (f.descender + 0.212).abs < 0.001
      && ((f.glyph a).advance - 1366 / 2048).abs < 1.0e-9)) && ok
  ok := (← check s!"kerning: A/V pulls together ({f.kern a v} em), 'AV' narrower than 'A'+'V'"
    (f.kern a v < 0 && measure f "AV" 100 < measure f "A" 100 + measure f "V" 100)) && ok
  -- composite glyphs (accented letters) contribute their base outline
  let comp := (f.glyph (f.glyphIndex 'é')).path.cmds.size
  let base := (f.glyph (f.glyphIndex 'e')).path.cmds.size
  ok := (← check s!"composite glyph 'é' ({comp} commands) ⊇ 'e' ({base})" (comp > base)) && ok
  let text := "the quick brown fox jumps over the lazy dog again and again"
  let lines := wrap f text 16 150
  ok := (← check s!"wrap at 150 px: {lines.size} lines, all ≤ 150 px, words preserved"
    (lines.size > 1 && lines.all (measure f · 16 ≤ 150)
      && " ".intercalate lines.toList == text)) && ok
  ok := (← check "wrap keeps explicit newlines and an over-long word"
    (wrap f "a\nsupercalifragilistic b" 16 40 == #["a", "supercalifragilistic", "b"])) && ok
  -- GPU program vs CPU on TrueType text (paths with quadratic curves)
  let ops := linesOps f #["AVA Wave ñé", "Lean 4 · 12px"] 22 (Color.hex 0x0D47A1) ⟨4, 2⟩
    ++ linesOps f #["small text, kerning: To Ty"] 11 Color.darkGray ⟨4, 60⟩
  let gpu := (GPU.referenceRender 200 80 ops).data
  let cpu := (Raster.render 200 80 ops).data
  let mut mx := 0
  for i in [0:cpu.size] do
    let d := ((gpu[i]!.toNat : Int) - cpu[i]!.toNat).natAbs
    if d > mx then mx := d
  ok := (← check s!"text: {ops.size} glyph fills, interpreted shader vs CPU: max error {mx}"
    (mx ≤ 1)) && ok
  return ok

end Tests.Text
