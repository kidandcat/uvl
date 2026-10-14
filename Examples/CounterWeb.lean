import UVL
import Examples.Counter

/-! Browser build of the counter example (see `web/`). The web shell calls
`uvl_web_make` once with the canvas size, then drives the returned runtime
through the exported `UVL.AnyRuntime` functions. -/

@[export uvl_web_make]
def Examples.CounterWeb.make (w h : UInt32) : UVL.AnyRuntime :=
  .start Examples.Counter.app w h
