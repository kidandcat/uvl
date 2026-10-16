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
  -- MSDF: close to the exact outlines, and the GPU program matches the CPU
  let outl := (Raster.render 240 70 (linesOps f #["Wave ßé@"] 48 Color.black ⟨4, 4⟩)).data
  let msdf := (Raster.render 240 70 (linesOpsMSDF f #["Wave ßé@"] 48 (.solid Color.black) ⟨4, 4⟩)).data
  let mut sum := 0
  let mut big := 0
  for i in [0:outl.size] do
    let d := ((outl[i]!.toNat : Int) - msdf[i]!.toNat).natAbs
    sum := sum + d
    if d > 64 then big := big + 1
  let mean := sum.toFloat / outl.size.toFloat
  ok := (← check s!"MSDF vs outlines at 48 px: mean |Δ| {mean}, {big} bytes off by > 64"
    (mean < 1.0 && big * 1000 < outl.size)) && ok
  -- at UI sizes: how far MSDF coverage strays from the exact outline coverage
  for sz in [11.0, 14.0, 16.0] do
    let line := "The quick brown fox jumps over 12 lazy dogs"
    let o := (Raster.render 400 30 (linesOps f #[line] sz Color.black ⟨4, 4⟩)).data
    let m := (Raster.render 400 30 (linesOpsMSDF f #[line] sz (.solid Color.black) ⟨4, 4⟩)).data
    let mut tot := 0
    let mut ink := 0
    let mut worst := 0
    for i in [0:o.size] do
      if i % 4 == 0 then
        let a := 255 - o[i]!.toNat
        let b := 255 - m[i]!.toNat
        tot := tot + (if a > b then a - b else b - a)
        ink := ink + a
        worst := Max.max worst (if a > b then a - b else b - a)
    ok := (← check s!"MSDF vs outlines at {sz} px: coverage error {(tot.toFloat / ink.toFloat * 100)}% of the ink, worst pixel {worst}/255"
      (tot * 4 < ink)) && ok
  let ops2 := Examples.msdfText
  let b := GPU.Batch.build 560 260 ops2
  let gpu := (GPU.referenceRender 560 260 ops2).data
  let cpu := (Raster.render 560 260 ops2).data
  let mut mx2 := 0
  for i in [0:cpu.size] do
    let d := ((gpu[i]!.toNat : Int) - cpu[i]!.toNat).natAbs
    if d > mx2 then mx2 := d
  ok := (← check s!"MSDF scene: {b.count} quads, {b.atlasGlyphs.size} atlas glyphs, interpreted shader vs CPU: max error {mx2}"
    (mx2 ≤ 1 && b.atlasGlyphs.size == (b.atlasGlyphs.toList.eraseDups).length)) && ok
  return ok

end Tests.Text
