import UVL.Anim.Basic
import UVL.UI.Basic

/-!
# From the proved clock to pixels

`UVL.Anim.Basic` never mentions `Float`. Two conversions cross into the renderer:

* `millisOfFloat` turns a runtime `tick` (`Float` seconds) into whole milliseconds.
  That is the only lossy step. After it, the clock is an `Int` and every sample is
  a `Rat`. Dropped frames are a larger millisecond delta; `Clip.schedules_agree`
  says the sample depends only on the sum.
* `natOfPixel` is `toPixel` followed by `Int.toNat` (`0` when negative).
  `toPixel_intCast` says an integer target is that integer. `Nat.toF` then stores
  it in a `Rect`. For coordinates below `2^30` that cast is the library's exact
  integer-to-float path (`UVL.Core.FloatLit`). Equality of the resulting `Float`
  with the real number is not a Lean proof: `Float` is an opaque IEEE type.
  What is proved is the integer the widget is placed at.

`withByteAlpha` stores a proved byte as `n / 255` in `Color.a`. `Color.toByte`
rounding that float back is tested, not proved.
-/

namespace UVL.Anim

/-- Nearest millisecond, clamped at `0` for a non-positive `dt`.
Not part of the proved core. -/
def millisOfFloat (dt : Float) : Int :=
  if dt ≤ 0 then 0 else ((dt * 1000).round.floor.toUInt64.toNat : Int)

/-- Pixel used by layout. Negative values become `0` (`Int.toNat`). -/
def natOfPixel (n : Int) : Nat := n.toNat

end UVL.Anim

namespace UVL.UI

open Anim

variable {Msg : Type}

/-- Place `child` with its top-left at a proved pixel. The offset is a layout
padding, so the child's rectangle is that integer, not a rounded float. -/
def shift (x y : Int) (child : Widget Msg) : Widget Msg :=
  .padding (natOfPixel x) (natOfPixel y) 0 0 child

/-- `Color.a` for a byte from `toUnitByte`. See the module note. -/
def withByteAlpha (c : Color) (byte : Int) : Color :=
  let n := if byte ≤ 0 then (0 : Nat) else if byte ≥ 255 then 255 else byte.toNat
  c.withAlpha (n.toF / 255)

end UVL.UI
