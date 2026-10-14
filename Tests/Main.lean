import Examples.Scenes
import Tests.PngDecode

/-!
Test driver (`lake test`).

* Golden images: each scene is rendered and compared with `Tests/golden/<name>.png`
  (decoded, with a tiny per-channel tolerance so the suite is robust to last-ulp
  differences of libm across platforms). Run `lake test -- --update` to regenerate.
* Layout checks: concrete positions for the roadmap example, and the
  `Admits` invariant re-checked at runtime over a sweep of constraints.
* Codec checks: PNG round-trip through our encoder and the test decoder.
-/

open UViz UViz.Layout

structure Golden where
  name : String
  w : Nat
  h : Nat
  png : Unit → ByteArray

def goldens : List Golden := [
  ⟨"primitives", 480, 320, fun _ => Image.toPNG (Raster.render 480 320 Examples.primitives)⟩,
  ⟨"hello", 320, 160, fun _ => Image.toPNG (UI.render Examples.hello 320 160 (Color.hex 0xECEFF1))⟩,
  ⟨"dashboard", 800, 600, fun _ =>
    Image.toPNG (UI.render Examples.dashboard 800 600 (Color.hex 0xF5F7FA))⟩
]

/-- Max channel difference allowed, and fraction of bytes allowed to differ. -/
def tolerance : Nat := 2

def compare (a b : ByteArray) : Nat × Nat := Id.run do
  let mut maxDiff := 0
  let mut nDiff := 0
  for i in [0:a.size] do
    let x := a[i]!.toNat; let y := b[i]!.toNat
    let d := if x > y then x - y else y - x
    if d > 0 then nDiff := nDiff + 1
    if d > maxDiff then maxDiff := d
  return (maxDiff, nDiff)

def checkGolden (update : Bool) (g : Golden) : IO Bool := do
  let path : System.FilePath := s!"Tests/golden/{g.name}.png"
  let actual := g.png ()
  if update || !(← path.pathExists) then
    IO.FS.writeBinFile path actual
    IO.println s!"  [updated] {g.name}"
    return true
  let expected ← IO.FS.readBinFile path
  if expected == actual then
    IO.println s!"  [ok] {g.name} (byte-identical)"
    return true
  match Tests.Png.decode expected, Tests.Png.decode actual with
  | .ok (ew, eh, ed), .ok (aw, ah, ad) =>
    if ew != aw || eh != ah then
      IO.println s!"  [FAIL] {g.name}: size {aw}x{ah}, expected {ew}x{eh}"
      return false
    let (maxDiff, nDiff) := compare ed ad
    if maxDiff <= tolerance then
      IO.println s!"  [ok] {g.name} ({nDiff} bytes within ±{tolerance})"
      return true
    IO.FS.createDirAll "Tests/out"
    IO.FS.writeBinFile s!"Tests/out/{g.name}.png" actual
    IO.println s!"  [FAIL] {g.name}: {nDiff} bytes differ, max Δ {maxDiff}; see Tests/out/{g.name}.png"
    return false
  | .error e, _ | _, .error e =>
    IO.println s!"  [FAIL] {g.name}: decode error {e}"
    return false

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  [{if cond then "ok" else "FAIL"}] {name}"
  return cond

def layoutTests : IO Bool := do
  let rects := (layout Examples.hello (Constraints.tight ⟨320, 160⟩)).node.rects 0 0
  let t1 ← check "hello: card centered, row content placed" (rects ==
    [(0, 0, 320, 160), (74, 49, 172, 62), (74, 49, 172, 62), (90, 65, 140, 30), (90, 65, 140, 30),
     (90, 73, 46, 14), (144, 65, 86, 30), (144, 65, 86, 30), (158, 73, 58, 14)])
  -- Re-check the (already proved) Admits invariant at runtime over a sweep.
  let widgets := [Examples.hello, Examples.dashboard, UI.text "overflowing text that is long",
    UI.row [UI.box 500 20, UI.box 500 20], UI.col [UI.spacer, UI.box 10 10, UI.spacer 2]]
  let mut allOk := true
  for w in widgets do
    for (mw, mh) in [(0, 0), (10, 5), (100, 50), (320, 240), (1000, 800)] do
      for (nw, nh) in [(0, 0), (mw / 2, mh / 2), (mw, mh)] do
        let c : Constraints := ⟨Min.min nw mw, mw, Min.min nh mh, mh, Nat.min_le_right _ _, Nat.min_le_right _ _⟩
        let r := layout w c
        -- every node lies within the root
        let inside := (r.node.rects 0 0).all fun (x, y, cw, ch) =>
          x + cw ≤ r.size.w && y + ch ≤ r.size.h
        if !(decide (c.Admits r.size)) || !inside then allOk := false
  let t2 ← check "layout sweep: sizes admitted, all nodes inside root" allOk
  let flex := layout (UI.row [UI.spacer, UI.box 40 10, UI.spacer 3] (gap := 0)) (Constraints.tight ⟨200, 10⟩)
  let t3 ← check "flex: spacers share free space 1:3"
    ((flex.node.rects 0 0).map (·.1) == [0, 0, 40, 80])
  return t1 && t2 && t3

def codecTests : IO Bool := do
  let fb := Raster.render 37 23 Examples.primitives (Color.hex 0x123456)
  let ok := match Tests.Png.decode (Image.toPNG fb) with
    | .ok (w, h, d) => w == 37 && h == 23 && d == fb.data
    | .error _ => false
  check "PNG round-trip (odd size, all filters)" ok

def main (args : List String) : IO UInt32 := do
  let update := args.contains "--update"
  IO.println "golden images:"
  let mut ok := true
  for g in goldens do
    ok := (← checkGolden update g) && ok
  IO.println "layout:"
  ok := (← layoutTests) && ok
  IO.println "codecs:"
  ok := (← codecTests) && ok
  IO.println (if ok then "ALL TESTS PASSED" else "SOME TESTS FAILED")
  return if ok then 0 else 1
