import UVL.Core.Geometry
import UVL.Core.Scalar

/-!
# Signed distance fields

Exact signed distance functions (negative inside) for the primitives that the
rasterizer draws analytically. A pixel's coverage is derived from the distance
at its center, which gives anti-aliased edges, rounded corners, borders and
soft shadows at essentially no extra cost.
-/

namespace UVL.SDF

@[inline] def clamp (x lo hi : Float) : Float := if x < lo then lo else if x > hi then hi else x

/-- Coverage of a pixel whose center is at signed distance `d` (1px box filter). -/
@[inline] def coverage (d : Float) : Float := Scalar.coverage d

@[inline] def circle (p c : Vec2) (r : Float) : Float := Scalar.circle p.x p.y c.x c.y r

/-- Corner radii, clockwise from top-left. -/
structure Corners where
  tl : Float := 0
  tr : Float := 0
  br : Float := 0
  bl : Float := 0
deriving Inhabited, Repr, BEq

def Corners.all (r : Float) : Corners := ⟨r, r, r, r⟩

/-- Rounded box centered at `c` with half extents `b` (Inigo Quilez' formula). -/
@[inline] def roundedBox (p c b : Vec2) (rad : Corners) : Float :=
  Scalar.roundedBox p.x p.y c.x c.y b.x b.y rad.tl rad.tr rad.br rad.bl

@[inline] def box (p c b : Vec2) : Float := roundedBox p c b {}

/-- Distance to the segment `ab`. -/
@[inline] def segment (p a b : Vec2) : Float :=
  let pa := p - a
  let ba := b - a
  let l2 := ba.dot ba
  let t := if l2 == 0 then 0 else clamp (pa.dot ba / l2) 0 1
  (pa - t * ba).length

/-- Approximate ellipse distance (exact on the axes, good enough for AA edges). -/
@[inline] def ellipse (p c : Vec2) (rx ry : Float) : Float :=
  let q := p - c
  let k0 := (Vec2.mk (q.x / rx) (q.y / ry)).length
  let k1 := (Vec2.mk (q.x / (rx * rx)) (q.y / (ry * ry))).length
  if k1 == 0 then -(Min.min rx ry) else k0 * (k0 - 1.0) / k1

/-- Abramowitz–Stegun approximation of `erf`, max error 1.5e-7. -/
def erf (x : Float) : Float :=
  let s := if x < 0 then -1.0 else 1.0
  let x := x.abs
  let t := 1.0 / (1.0 + 0.3275911 * x)
  let y := 1.0 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t
    - 0.284496736) * t + 0.254829592) * t * Float.exp (-x * x)
  s * y

/-- Coverage of a shape blurred by a Gaussian of std-dev `sigma`, from its distance. -/
@[inline] def blurredCoverage (d sigma : Float) : Float :=
  if sigma <= 0.0 then coverage d else 0.5 * (1.0 - erf (d / (sigma * 1.41421356237)))

end UVL.SDF
