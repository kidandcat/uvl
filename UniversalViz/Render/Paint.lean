import UniversalViz.Core.Color
import UniversalViz.Core.Geometry

/-!
# Paint

How a shape's interior is colored: a solid color or a linear/radial gradient.
-/

namespace UViz

/-- A gradient stop: offset in `[0, 1]` and color. -/
abbrev Stop := Float × Color

inductive Paint where
  | solid (c : Color)
  | linear (p0 p1 : Vec2) (stops : Array Stop)
  | radial (center : Vec2) (radius : Float) (stops : Array Stop)
deriving Inhabited

instance : Coe Color Paint := ⟨Paint.solid⟩

namespace Paint

def sampleStops (stops : Array Stop) (t : Float) : Color := Id.run do
  if stops.isEmpty then return Color.transparent
  let t := if t < 0 then 0 else if t > 1 then 1 else t
  let first := stops[0]!
  if t <= first.1 then return first.2
  let mut prev := first
  for s in stops do
    if t <= s.1 then
      let span := s.1 - prev.1
      let k := if span <= 0 then 0 else (t - prev.1) / span
      return Color.lerp prev.2 s.2 k
    prev := s
  return prev.2

/-- Color of the paint at point `p` (in the paint's local coordinates). -/
@[inline] def colorAt : Paint → Vec2 → Color
  | .solid c, _ => c
  | .linear p0 p1 stops, p =>
    let d := p1 - p0
    let l2 := d.dot d
    sampleStops stops (if l2 == 0 then 0 else (p - p0).dot d / l2)
  | .radial c r stops, p => sampleStops stops (if r == 0 then 0 else (p - c).length / r)

def isSolid : Paint → Bool
  | .solid _ => true
  | _ => false

end Paint

end UViz
