import UniversalViz.Core.FloatLit

/-!
# Geometry

Floating point vectors, rectangles and 2D affine transforms used by the
scene graph and the rasterizer.
-/

namespace UViz

structure Vec2 where
  x : Float
  y : Float
deriving Inhabited, Repr

namespace Vec2
instance : Add Vec2 := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩
instance : Sub Vec2 := ⟨fun a b => ⟨a.x - b.x, a.y - b.y⟩⟩
instance : Neg Vec2 := ⟨fun a => ⟨-a.x, -a.y⟩⟩
instance : HMul Float Vec2 Vec2 := ⟨fun k a => ⟨k * a.x, k * a.y⟩⟩
instance : SMul Float Vec2 := ⟨fun k a => ⟨k * a.x, k * a.y⟩⟩
def zero : Vec2 := ⟨0, 0⟩
@[inline] def dot (a b : Vec2) : Float := a.x * b.x + a.y * b.y
@[inline] def cross (a b : Vec2) : Float := a.x * b.y - a.y * b.x
@[inline] def length (a : Vec2) : Float := Float.sqrt (a.dot a)
@[inline] def abs (a : Vec2) : Vec2 := ⟨a.x.abs, a.y.abs⟩
@[inline] def max (a b : Vec2) : Vec2 := ⟨Max.max a.x b.x, Max.max a.y b.y⟩
@[inline] def min (a b : Vec2) : Vec2 := ⟨Min.min a.x b.x, Min.min a.y b.y⟩
def lerp (a b : Vec2) (t : Float) : Vec2 := ⟨a.x + (b.x - a.x) * t, a.y + (b.y - a.y) * t⟩
end Vec2

/-- Axis-aligned rectangle: top-left corner plus size. -/
structure Rect where
  x : Float
  y : Float
  w : Float
  h : Float
deriving Inhabited, Repr

namespace Rect
def center (r : Rect) : Vec2 := ⟨r.x + r.w / 2, r.y + r.h / 2⟩
def halfSize (r : Rect) : Vec2 := ⟨r.w / 2, r.h / 2⟩
def inflate (r : Rect) (d : Float) : Rect := ⟨r.x - d, r.y - d, r.w + 2 * d, r.h + 2 * d⟩
def translate (r : Rect) (d : Vec2) : Rect := { r with x := r.x + d.x, y := r.y + d.y }
def contains (r : Rect) (p : Vec2) : Bool :=
  p.x >= r.x && p.y >= r.y && p.x < r.x + r.w && p.y < r.y + r.h
def ofPoints (ps : Array Vec2) : Rect :=
  if ps.isEmpty then ⟨0, 0, 0, 0⟩ else
  let lo := ps.foldl Vec2.min ps[0]!
  let hi := ps.foldl Vec2.max ps[0]!
  ⟨lo.x, lo.y, hi.x - lo.x, hi.y - lo.y⟩
def corners (r : Rect) : Array Vec2 :=
  #[⟨r.x, r.y⟩, ⟨r.x + r.w, r.y⟩, ⟨r.x + r.w, r.y + r.h⟩, ⟨r.x, r.y + r.h⟩]
end Rect

/-- 2D affine transform `p ↦ (a*x + c*y + e, b*x + d*y + f)`. -/
structure Affine where
  a : Float := 1
  b : Float := 0
  c : Float := 0
  d : Float := 1
  e : Float := 0
  f : Float := 0
deriving Inhabited, Repr

namespace Affine
def identity : Affine := {}
def translate (dx dy : Float) : Affine := { e := dx, f := dy }
def scale (sx sy : Float) : Affine := { a := sx, d := sy }
def rotate (θ : Float) : Affine :=
  let co := Float.cos θ; let si := Float.sin θ
  { a := co, b := si, c := -si, d := co }
@[inline] def apply (m : Affine) (p : Vec2) : Vec2 :=
  ⟨m.a * p.x + m.c * p.y + m.e, m.b * p.x + m.d * p.y + m.f⟩
/-- `m.compose n` applies `n` first, then `m`. -/
def compose (m n : Affine) : Affine :=
  { a := m.a * n.a + m.c * n.b
    b := m.b * n.a + m.d * n.b
    c := m.a * n.c + m.c * n.d
    d := m.b * n.c + m.d * n.d
    e := m.a * n.e + m.c * n.f + m.e
    f := m.b * n.e + m.d * n.f + m.f }
def det (m : Affine) : Float := m.a * m.d - m.b * m.c
def inverse (m : Affine) : Affine :=
  let k := m.det
  let k := if k == 0 then 1 else 1 / k
  { a := m.d * k, b := -m.b * k, c := -m.c * k, d := m.a * k
    e := (m.c * m.f - m.d * m.e) * k
    f := (m.b * m.e - m.a * m.f) * k }
/-- Average linear scale factor, used to convert SDF distances back to pixels. -/
def scaleFactor (m : Affine) : Float := Float.sqrt m.det.abs
def isIdentity (m : Affine) : Bool :=
  m.a == 1 && m.b == 0 && m.c == 0 && m.d == 1 && m.e == 0 && m.f == 0
def mapRect (m : Affine) (r : Rect) : Rect := Rect.ofPoints (r.corners.map m.apply)
end Affine

end UViz
