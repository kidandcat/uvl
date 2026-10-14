import UVL.Core.Geometry

/-!
# Vector paths

Paths made of lines and quadratic/cubic Bézier curves. They are flattened into
polylines (in device space) before rasterization.
-/

namespace UVL

inductive PathCmd where
  | moveTo (p : Vec2)
  | lineTo (p : Vec2)
  | quadTo (c p : Vec2)
  | cubicTo (c1 c2 p : Vec2)
  | close
deriving Inhabited, Repr

structure Path where
  cmds : Array PathCmd := #[]
deriving Inhabited, Repr

namespace Path

def moveTo (p : Path) (x y : Float) : Path := ⟨p.cmds.push (.moveTo ⟨x, y⟩)⟩
def lineTo (p : Path) (x y : Float) : Path := ⟨p.cmds.push (.lineTo ⟨x, y⟩)⟩
def quadTo (p : Path) (cx cy x y : Float) : Path := ⟨p.cmds.push (.quadTo ⟨cx, cy⟩ ⟨x, y⟩)⟩
def cubicTo (p : Path) (c1x c1y c2x c2y x y : Float) : Path :=
  ⟨p.cmds.push (.cubicTo ⟨c1x, c1y⟩ ⟨c2x, c2y⟩ ⟨x, y⟩)⟩
def close (p : Path) : Path := ⟨p.cmds.push .close⟩

/-- Polygon through the given points. -/
def polygon (pts : Array Vec2) : Path := Id.run do
  if h : 0 < pts.size then
    let mut p : Path := ⟨#[.moveTo pts[0]]⟩
    for q in pts[1:] do p := ⟨p.cmds.push (.lineTo q)⟩
    return p.close
  else return {}

/-- Open polyline through the given points. -/
def polyline (pts : Array Vec2) : Path := Id.run do
  if h : 0 < pts.size then
    let mut p : Path := ⟨#[.moveTo pts[0]]⟩
    for q in pts[1:] do p := ⟨p.cmds.push (.lineTo q)⟩
    return p
  else return {}

/-- Regular star / polygon helper. -/
def star (c : Vec2) (outer inner : Float) (points : Nat) : Path :=
  let n := 2 * points
  polygon <| (Array.range n).map fun i =>
    let θ := (i.toF / n.toF) * 2.0 * 3.14159265358979 - 3.14159265358979 / 2.0
    let r := if i % 2 == 0 then outer else inner
    ⟨c.x + r * Float.cos θ, c.y + r * Float.sin θ⟩

/-- A flattened sub-path: points in device space and whether it was closed. -/
structure Poly where
  pts : Array Vec2
  closed : Bool
deriving Inhabited

private def segmentsFor (len : Float) : Nat :=
  let n := (len / 3.0).ceil.toUInt64.toNat
  if n < 2 then 2 else if n > 128 then 128 else n

/-- Flatten the path through transform `m` into polylines. -/
def flatten (path : Path) (m : Affine) : Array Poly := Id.run do
  let mut out : Array Poly := #[]
  let mut cur : Array Vec2 := #[]
  let mut last : Vec2 := ⟨0, 0⟩
  let mut start : Vec2 := ⟨0, 0⟩
  for cmd in path.cmds do
    match cmd with
    | .moveTo p =>
      if cur.size > 1 then out := out.push ⟨cur, false⟩
      let q := m.apply p
      cur := #[q]; last := q; start := q
    | .lineTo p =>
      let q := m.apply p
      if cur.isEmpty then cur := #[last]
      cur := cur.push q; last := q
    | .quadTo c p =>
      let c := m.apply c; let p := m.apply p
      if cur.isEmpty then cur := #[last]
      let n := segmentsFor ((c - last).length + (p - c).length)
      let p0 := last
      for i in [1:n+1] do
        let t := i.toF / n.toF
        let u := 1.0 - t
        cur := cur.push ((u * u) • p0 + (2.0 * u * t) • c + (t * t) • p)
      last := p
    | .cubicTo c1 c2 p =>
      let c1 := m.apply c1; let c2 := m.apply c2; let p := m.apply p
      if cur.isEmpty then cur := #[last]
      let n := segmentsFor ((c1 - last).length + (c2 - c1).length + (p - c2).length)
      let p0 := last
      for i in [1:n+1] do
        let t := i.toF / n.toF
        let u := 1.0 - t
        cur := cur.push ((u * u * u) • p0 + (3.0 * u * u * t) • c1 + (3.0 * u * t * t) • c2
          + (t * t * t) • p)
      last := p
    | .close =>
      if cur.size > 1 then out := out.push ⟨cur, true⟩
      cur := #[]; last := start
  if cur.size > 1 then out := out.push ⟨cur, false⟩
  return out

end Path

end UVL
