import Examples.Sprites

/-! Android build of the sprites example: `android/build.sh Examples.SpritesAndroid`. -/

namespace Examples.SpritesAndroid

@[export uvl_android_make]
def make (w h : UInt32) : UVL.AnyRuntime :=
  .start (Examples.Sprites.app w.toNat h.toNat) w h

end Examples.SpritesAndroid
