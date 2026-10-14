import Examples.Scenes

open UViz

def main : IO Unit := do
  IO.FS.createDirAll "out"
  let fb := Raster.render 480 320 Examples.primitives
  Image.writePNG "out/primitives.png" fb
  Image.writePPM "out/primitives.ppm" fb
  IO.println "wrote out/primitives.png"
