import UVLWindow
import Examples.Sprites

/-! Desktop window for the sprites example: `lake exe uvl-sprites [units] [zoom]`. -/

def main (args : List String) : IO Unit := do
  let units := (args[0]? >>= String.toNat?).getD 300
  let zoom := ((args[1]? >>= String.toNat?).map (·.toFloat / 100)).getD 1
  UVL.SDL.run (Examples.Sprites.app 1280 720 units zoom) 1280 720
