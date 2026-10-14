import UVL
import Examples.Scenes

/-! Browser build of the static dashboard scene: charts, gradients, paths,
shadows and text. Used to check the GPU renderer against the CPU rasterizer on
a heavier scene than the counter (see `web/smoke.cjs`). -/

namespace Examples.DashboardWeb

def app : UVL.App Unit Unit where
  init := ()
  update _ m := m
  view _ := Examples.dashboard
  background := UVL.Color.hex 0xF5F7FA
  title := "uvl · dashboard"

@[export uvl_web_make]
def make (w h : UInt32) : UVL.AnyRuntime := .start app w h

end Examples.DashboardWeb
