# UVL on Android

The phone example ([`Examples/Phone.lean`](../Examples/Phone.lean)) as an Android app: a
counter with its history chart, a slider driving an animated level meter, toggles and a text
field with the on-screen keyboard. The APK contains no Java or Kotlin code. It is a
`NativeActivity` whose native library is the Lean app compiled to C plus a small C shell.

```
android/
  android_shell.c      NativeActivity main loop: touch and keys in, pixels out
  AndroidManifest.xml  one NativeActivity, no code (android:hasCode="false")
  build.sh             Lean runtime + Init + app for each ABI, then the APK
  lean_stubs.c         lean_initialize and lean_infer_type (the compiler is not linked)
  smoke.sh             install, launch, tap and type on an emulator or device (adb)
```

## Building

You need the Android NDK (r26 or newer), the Android SDK (build-tools and a platform, for
`aapt2`, `zipalign` and `apksigner`), a JDK, cmake, git and the Lean toolchain from
`lean-toolchain`.

```sh
export ANDROID_HOME=~/Library/Android/sdk          # or ~/Android/Sdk on Linux
export ANDROID_NDK_HOME=$ANDROID_HOME/ndk/27.2.12479018
android/build.sh                                     # android/dist/uvl-example.apk
adb install -r android/dist/uvl-example.apk
```

The first build takes a while: it compiles the Lean runtime and `Init` for each ABI and
caches them in `.lake/build/android`; after that only the app is recompiled.

| Variable | Default | |
| --- | --- | --- |
| `ANDROID_ABIS` | `arm64-v8a` | space-separated; also `x86_64` (emulators), `armeabi-v7a`, `x86` |
| `UVL_APK` | `android/dist/uvl-example.apk` | output path |
| `UVL_KEYSTORE`, `UVL_KEYSTORE_PASS`, `UVL_KEY_ALIAS` | generated debug key | signing key |

Another app module can be packaged with `android/build.sh My.Module`, as long as the module
exports its constructor as `uvl_android_make` (see
[`Examples/PhoneAndroid.lean`](../Examples/PhoneAndroid.lean)):

```lean
@[export uvl_android_make]
def make (w h : UInt32) : UVL.AnyRuntime := .start Examples.Phone.app w h
```

The app targets Android 9 (API 28) and newer. The native library is linked with 16 KB page
alignment, so it also loads on devices with 16 KB pages.

## How it works

Like the browser build ([`web/build.sh`](../web/build.sh)), the script builds what Lean only
ships as host code: the runtime (C++, from the sources of the exact toolchain version, with
libuv built for Android) and `Init` (C generated with `lean -c`). It compiles the C that Lake
generates for the app, links everything with the shell into `lib/<abi>/libuvl.so`, and packages
the APK with `aapt2`, `zipalign` and `apksigner`. Symbols that only compile-time code uses
(elaborators, `bv_decide` reflection) get stubs that panic if they are ever called.

The shell ([`android_shell.c`](android_shell.c)) uses `android_native_app_glue` and does what
the SDL and browser shells do:

- **Frames.** The app renders on the CPU at density-independent size: the window buffer is the
  screen divided by the display density (1080×2400 at 420 dpi becomes 411×914) and the
  compositor scales it to the screen. Only the damaged parts of a frame are re-rasterized
  (`uvl_host_present`); the result is copied into the window.
- **Insets.** The app gets the activity's content rect, the part of the window not covered by
  the status bar, the navigation bar or the keyboard, and is relaid out when it changes. The
  rest of the window is painted with the app's background.
- **Touch.** The first finger is the pointer: down, move and up become pointer events, and
  lifting it also sends `pointer leave`, so nothing stays hovered.
- **Keyboard.** The on-screen keyboard is shown while a text input has the focus
  (`uvl_host_text_focus`), through `InputMethodManager` over JNI. Characters are decoded with
  `KeyEvent.getUnicodeChar`; Backspace, Enter, arrows and Ctrl shortcuts map to UVL keys. Back
  closes the keyboard (and blurs the input), otherwise it leaves the app.
- **Idle.** The loop blocks on the looper unless the app is animating
  (`uvl_host_animating`: a tween, a blinking caret, a hover fade), so an idle app uses no CPU.
- **Stack.** Lean code runs on its own thread with a 64 MB stack instead of the glue's 1 MB.

## Testing

CI builds the APK for `arm64-v8a` and `x86_64`, runs it on an x86_64 emulator (API 34, Pixel 6
profile at 420 dpi) and
checks with [`smoke.sh`](smoke.sh) that tapping "+" and typing into the text field change the
screen. The APK and the screenshots are uploaded as the `android-app` artifact.

```sh
ANDROID_ABIS="arm64-v8a x86_64" android/build.sh
android/smoke.sh                     # with an emulator running or a phone connected
```

## Not yet

- GPU rendering (the WGSL renderer through wgpu-native on Vulkan) is not wired up; frames are
  rasterized on the CPU.
- One pointer only: no multi-touch gestures.
- No clipboard integration and no IME composition (predictive text arrives as key events
  only, which is what most keyboards send to a `NativeActivity`).
