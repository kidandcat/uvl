import UVL

/-!
PNG decoder tests: fixtures written by Python's zlib (stored, fixed and dynamic
Huffman blocks, all five row filters, IDAT split in two chunks) in every 8-bit
color type, compared with the pixel formula that generated them.
-/

namespace Tests.PngDecode

open UVL

def W := 24
def H := 17

def r (x _ : Nat) : UInt8 := (x * 11 % 256).toUInt8
def g (_ y : Nat) : UInt8 := (y * 15 % 256).toUInt8
def b (x y : Nat) : UInt8 := ((x + y) * 7 % 256).toUInt8

def expected (px : Nat → Nat → UInt8 × UInt8 × UInt8 × UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for y in [0:H] do
    for x in [0:W] do
      let (r, g, b, a) := px x y
      out := out.push r |>.push g |>.push b |>.push a
  return out

def fixtures : List (String × ByteArray) := [
  ("rgba", expected fun x y => (r x y, g x y, b x y, (x * y * 3 % 256).toUInt8)),
  ("rgb", expected fun x y => (r x y, g x y, b x y, 255)),
  ("gray", expected fun x y => (r x y, r x y, r x y, 255)),
  ("graya", expected fun x y => (r x y, r x y, r x y, g x y)),
  ("palette", expected fun x y =>
    let k := (x + y) % 16
    ((k * 16).toUInt8, (255 - k * 16).toUInt8, (k * 7).toUInt8,
      if k < 8 then (k * 30).toUInt8 else 255))]

def check (name : String) (ok : Bool) : IO Bool := do
  IO.println s!"  [{if ok then "ok" else "FAIL"}] {name}"
  return ok

def run : IO Bool := do
  let mut ok := true
  for (name, want) in fixtures do
    let got := Image.decodePNG (← IO.FS.readBinFile s!"Tests/fixtures/{name}.png")
    ok := (← check s!"decode {name}.png" (match got with
      | .ok (w, h, d) => w == W && h == H && d == want
      | .error _ => false)) && ok
  let png ← IO.FS.readBinFile "Tests/fixtures/rgba.png"
  let corrupt := png.set! 60 (png[60]! ^^^ 0xFF)
  ok := (← check "corrupt chunk rejected" (match Image.decodePNG corrupt with
    | .error _ => true | .ok _ => false)) && ok
  return ok

end Tests.PngDecode
