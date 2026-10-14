import Examples.Controls

/-! Browser build of the controls example. -/

namespace Examples.ControlsWeb

@[export uvl_web_make]
def make (w h : UInt32) : UVL.AnyRuntime := .start Examples.Controls.app w h

end Examples.ControlsWeb
