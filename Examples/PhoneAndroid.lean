import Examples.Phone

/-! Android build of the phone example (`android/build.sh`). -/

namespace Examples.PhoneAndroid

@[export uvl_android_make]
def make (w h : UInt32) : UVL.AnyRuntime := .start Examples.Phone.app w h

end Examples.PhoneAndroid
