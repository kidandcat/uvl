import UVLWindow
import Examples.Counter

/-! Desktop window for the counter example (`lake exe uvl-counter`). -/

def main : IO Unit :=
  UViz.SDL.run Examples.Counter.app 480 360
