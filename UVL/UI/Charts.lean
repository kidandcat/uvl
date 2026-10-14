import UVL.UI.Basic

/-!
# Charts

Small chart widgets built on `canvas`: they lay out like any other widget and
paint with the same `RenderOp` primitives.
-/

namespace UVL.UI

variable {Msg : Type}

def palette : Array Color :=
  #[Color.hex 0x1E88E5, Color.hex 0x43A047, Color.hex 0xFB8C00, Color.hex 0x8E24AA,
    Color.hex 0xE53935, Color.hex 0x00897B]

private def maxVal (xs : List Float) : Float :=
  let m := xs.foldl (fun m x => if x > m then x else m) 0
  if m <= 0 then 1 else m

/-- Vertical bar chart with labels under each bar. -/
def barChart (data : List (String × Float)) (w : Nat := 320) (h : Nat := 200) : Widget Msg :=
  canvas w h fun r => Id.run do
    let n := data.length
    if n == 0 then return #[]
    let top := r.y + 8
    let base := r.y + r.h - 18
    let m := maxVal (data.map (·.2))
    let slot := (r.w - 16) / n.toF
    let mut ops : Array RenderOp :=
      #[RenderOp.line ⟨r.x + 8, base + 0.5⟩ ⟨r.x + r.w - 8, base + 0.5⟩ 1 Color.gray]
    for i in [0:4] do
      let gy := base - (base - top) * (i + 1).toF / 4
      ops := ops.push (RenderOp.line ⟨r.x + 8, gy⟩ ⟨r.x + r.w - 8, gy⟩ 1 (Color.gray.withAlpha 0.25))
    let mut i := 0
    for (label, v) in data do
      let bh := (base - top) * v / m
      let x := r.x + 8 + slot * i.toF + slot * 0.15
      let bw := slot * 0.7
      let col := palette[i % palette.size]!
      ops := ops.push (.fill (.roundedRect ⟨x, base - bh, bw, bh⟩ ⟨4, 4, 0, 0⟩)
        (.linear ⟨0, base - bh⟩ ⟨0, base⟩ #[(0, col), (1, col.withAlpha 0.6)]))
      let lw := (Font.widthCells label).toF
      ops := ops.push (.text ⟨x + bw / 2 - lw / 2, base + 6⟩ label 1 Color.darkGray)
      i := i + 1
    return ops

/-- Line chart of one or more series sharing the same x positions. -/
def lineChart (series : List (List Float)) (w : Nat := 320) (h : Nat := 200) : Widget Msg :=
  canvas w h fun r => Id.run do
    let all := series.foldl (· ++ ·) []
    let m := maxVal all
    let left := r.x + 10
    let right := r.x + r.w - 10
    let top := r.y + 10
    let base := r.y + r.h - 10
    let mut ops : Array RenderOp := #[]
    for i in [0:5] do
      let gy := base - (base - top) * i.toF / 4
      ops := ops.push (RenderOp.line ⟨left, gy⟩ ⟨right, gy⟩ 1 (Color.gray.withAlpha 0.3))
    let mut si := 0
    for s in series do
      let n := s.length
      let col := palette[si % palette.size]!
      let pts : Array Vec2 := (s.toArray.mapIdx fun i v =>
        ⟨left + (right - left) * i.toF / (Max.max (n - 1) 1).toF, base - (base - top) * v / m⟩)
      -- area under the curve
      if h : 0 < pts.size then
        let area := pts.push ⟨pts[pts.size - 1]!.x, base⟩ |>.push ⟨pts[0].x, base⟩
        ops := ops.push (RenderOp.path (Path.polygon area)
          (.linear ⟨0, top⟩ ⟨0, base⟩ #[(0, col.withAlpha 0.35), (1, col.withAlpha 0.0)]))
      ops := ops.push (RenderOp.strokePath (Path.polyline pts) 2.5 col)
      for p in pts do
        ops := ops.push (RenderOp.circle p 3.5 Color.white)
        ops := ops.push (.stroke (.circle p 3.5) 2 col)
      si := si + 1
    return ops

/-- Donut chart. -/
def donutChart (values : List Float) (size : Nat := 160) (thickness : Float := 26) : Widget Msg :=
  canvas size size fun r => Id.run do
    let total := values.foldl (· + ·) 0
    let total := if total <= 0 then 1 else total
    let c := r.center
    let ro := Min.min r.w r.h / 2 - 2
    let ri := ro - thickness
    let mut a0 := -3.14159265358979 / 2
    let mut ops : Array RenderOp := #[]
    let mut i := 0
    for v in values do
      let a1 := a0 + 2 * 3.14159265358979 * v / total
      let steps := Max.max 2 ((a1 - a0) * 24).ceil.toUInt64.toNat
      let outer := (Array.range (steps + 1)).map fun k =>
        let a := a0 + (a1 - a0) * k.toF / steps.toF
        Vec2.mk (c.x + ro * Float.cos a) (c.y + ro * Float.sin a)
      let inner := (Array.range (steps + 1)).reverse.map fun k =>
        let a := a0 + (a1 - a0) * k.toF / steps.toF
        Vec2.mk (c.x + ri * Float.cos a) (c.y + ri * Float.sin a)
      ops := ops.push (RenderOp.path (Path.polygon (outer ++ inner)) palette[i % palette.size]!)
      a0 := a1
      i := i + 1
    return ops

end UVL.UI
