import UVL.Core.FloatLit

/-!
# Color

Colors are stored as straight (non-premultiplied) RGBA floats in `[0, 1]`.
The frame buffer stores 8-bit straight RGBA; conversion happens at blend time.
-/

namespace UVL

structure Color where
  r : Float
  g : Float
  b : Float
  a : Float := 1.0
deriving Inhabited, Repr

namespace Color

@[inline] def clamp01 (x : Float) : Float :=
  if x < 0.0 then 0.0 else if x > 1.0 then 1.0 else x

def rgb (r g b : Float) : Color := { r, g, b }
def rgba (r g b a : Float) : Color := { r, g, b, a }

/-- `Color.hex 0xRRGGBB`. -/
def hex (v : Nat) (a : Float := 1.0) : Color :=
  { r := (v / 65536 % 256).toFloat / 255.0
    g := (v / 256 % 256).toFloat / 255.0
    b := (v % 256).toFloat / 255.0
    a }

def withAlpha (c : Color) (a : Float) : Color := { c with a }

def lerp (x y : Color) (t : Float) : Color :=
  { r := x.r + (y.r - x.r) * t
    g := x.g + (y.g - x.g) * t
    b := x.b + (y.b - x.b) * t
    a := x.a + (y.a - x.a) * t }

@[inline] def toByte (x : Float) : UInt8 :=
  (clamp01 x * 255.0 + 0.5).floor.toUInt8

def transparent : Color := { r := 0, g := 0, b := 0, a := 0 }
def black : Color := rgb 0 0 0
def white : Color := rgb 1 1 1
def red : Color := hex 0xE53935
def green : Color := hex 0x43A047
def blue : Color := hex 0x1E88E5
def yellow : Color := hex 0xFDD835
def orange : Color := hex 0xFB8C00
def purple : Color := hex 0x8E24AA
def teal : Color := hex 0x00897B
def gray : Color := hex 0x9E9E9E
def darkGray : Color := hex 0x424242
def lightGray : Color := hex 0xEEEEEE

end Color

end UVL
