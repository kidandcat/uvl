import UVLWindow
import Examples.Controls

/-! Desktop window for the controls example (`lake exe uvl-controls`). -/

def main : IO Unit :=
  UVL.SDL.run Examples.Controls.app 960 360
