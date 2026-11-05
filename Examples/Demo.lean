import Examples.Scenes
import Examples.Anim

open UVL

def main : IO Unit := do
  IO.FS.createDirAll "out"
  let fb := Raster.render 480 320 Examples.primitives
  Image.writePNG "out/primitives.png" fb
  Image.writePPM "out/primitives.ppm" fb
  Image.writePNG "out/hello.png" (UI.render Examples.hello 320 160 (Color.hex 0xECEFF1))
  Image.writePNG "out/dashboard.png" (UI.render Examples.dashboard 800 600 (Color.hex 0xF5F7FA))
  Image.writePNG "out/anim-start.png" (Examples.Anim.renderAt (Examples.Anim.atMs 0))
  Image.writePNG "out/anim-mid.png" (Examples.Anim.renderAt (Examples.Anim.atMs 400))
  Image.writePNG "out/anim-end.png" (Examples.Anim.renderAt (Examples.Anim.atMs 800))
  Image.writePNG "out/anim-reverse.png" (Examples.Anim.renderAt Examples.Anim.reversed)
  IO.println "wrote out/primitives.png, out/hello.png, out/dashboard.png, out/anim-*.png"
