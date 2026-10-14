import UVL.GPU.Reference
import Examples.Scenes
import Examples.Counter

/-!
GPU pipeline checks without a GPU: the shader functions of the DSL agree with
`UVL.SDF`, and whole scenes rendered through the lowered primitives and the
interpreted fragment program match the CPU rasterizer.
-/

namespace Tests.GPU
open UVL UVL.GPU

def check (name : String) (cond : Bool) : IO Bool := do
  IO.println s!"  [{if cond then "ok" else "FAIL"}] {name}"
  return cond

/-- Largest per-channel difference and number of differing bytes. -/
def compare (a b : ByteArray) : Nat × Nat := Id.run do
  let mut mx := 0
  let mut n := 0
  for i in [0:Min.min a.size b.size] do
    let d := ((a[i]!.toNat : Int) - b[i]!.toNat).natAbs
    if d > 0 then n := n + 1
    if d > mx then mx := d
  return (mx, n)

def evalF (f : FnDef) (args : List Value) : Float :=
  match f.eval functions args with
  | ⟨.f32, v⟩ => v
  | _ => 0.0 / 0.0

def v2 (x y : Float) : Value := ⟨.v2, ⟨x, y⟩⟩
def f (x : Float) : Value := ⟨.f32, x⟩

/-- Shader SDFs vs `UVL.SDF` on a grid of points. -/
def sdfAgree : Bool := Id.run do
  let mut ok := true
  for i in [0:21] do
    for j in [0:21] do
      let p : Vec2 := ⟨i.toF * 3.0 - 30.0, j.toF * 2.5 - 25.0⟩
      let c : Vec2 := ⟨1.5, -2.0⟩
      let rad : SDF.Corners := ⟨2, 4, 6, 8⟩
      let near (a b : Float) := (a - b).abs < 1.0e-9
      ok := ok && near (evalF sdCircleDef.1 [v2 p.x p.y, v2 c.x c.y, f 7]) (SDF.circle p c 7)
      ok := ok && near (evalF sdRoundedBoxDef.1 [v2 p.x p.y, v2 c.x c.y, v2 12 9, ⟨.v4, ⟨2, 4, 6, 8⟩⟩])
        (SDF.roundedBox p c ⟨12, 9⟩ rad)
      ok := ok && near (evalF sdSegmentDef.1 [v2 p.x p.y, v2 c.x c.y, v2 20 11])
        (SDF.segment p c ⟨20, 11⟩)
      ok := ok && near (evalF sdEllipseDef.1 [v2 p.x p.y, v2 c.x c.y, f 14, f 6])
        (SDF.ellipse p c 14 6)
      ok := ok && near (evalF erfDef.1 [f (p.x / 10)]) (SDF.erf (p.x / 10))
  return ok

structure Scene where
  name : String
  w : Nat
  h : Nat
  ops : Array RenderOp
  bg : Color

def counterScene : Scene :=
  let rt := Runtime.start Examples.Counter.app 320 240
  ⟨"counter", 320, 240, rt.tree.2.toOps 0 0 rt.pointerState, rt.app.background⟩

def scenes : List Scene := [
  ⟨"primitives", 480, 320, Examples.primitives, Color.white⟩,
  ⟨"hello", 320, 160, Examples.hello.toOps 320 160, Color.hex 0xECEFF1⟩,
  counterScene
]

def run : IO Bool := do
  let mut ok ← check "shader SDFs (circle, rounded box, segment, ellipse, erf) == UVL.SDF" sdfAgree
  for s in scenes do
    let t0 ← IO.monoMsNow
    let (mx, n) := compare (referenceRender s.w s.h s.ops s.bg).data (Raster.render s.w s.h s.ops s.bg).data
    let t1 ← IO.monoMsNow
    let prims := (Batch.build s.w s.h s.ops).count
    ok := (← check s!"{s.name}: {prims} GPU primitives, interpreted shader vs CPU: max error {mx}, {n} bytes differ ({t1 - t0} ms)" (mx ≤ 1)) && ok
  return ok

end Tests.GPU
