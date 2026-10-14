import UVL
import Examples.Scenes

/-! Browser build of a static text scene: TrueType outlines (`typography`) and
MSDF glyphs (`msdfText`), so the smoke test checks the GPU atlas path against
the CPU rasterizer (see `web/smoke.cjs`). -/

namespace Examples.TextWeb

open UVL UI

def app : App Unit Unit where
  init := ()
  update _ m := m
  view _ := col (gap := 0) [typography, canvas 560 260 fun r => #[.translate r.x r.y Examples.msdfText]]
  background := Color.hex 0xECEFF1
  title := "uvl · text"

@[export uvl_web_make]
def make (w h : UInt32) : AnyRuntime := .start app w h

end Examples.TextWeb
