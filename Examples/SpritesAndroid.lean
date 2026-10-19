import Examples.Sprites
import UVLGPU

/-! Android build of the sprites example: `android/build.sh Examples.SpritesAndroid`.
Importing `UVLGPU` makes the build link the WebGPU renderer (drawn on Vulkan,
with the CPU rasterizer as the fallback). -/

namespace Examples.SpritesAndroid

@[export uvl_android_make]
def make (w h : UInt32) : UVL.AnyRuntime :=
  .start (Examples.Sprites.app w.toNat h.toNat) w h

end Examples.SpritesAndroid
