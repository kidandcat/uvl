import Lake
open Lake DSL

package uvl where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
  moreLeancArgs := #["-O3"]

@[default_target]
lean_lib UVL

lean_lib Tests where
  globs := #[.one `Tests.PngDecode, .one `Tests.Tile, .one `Tests.Damage, .one `Tests.GPU, .one `Tests.Text, .one `Tests.Controls, .one `Tests.Html, .one `Tests.Camera]

lean_lib Examples where
  globs := #[.one `Examples.Scenes, .one `Examples.Counter, .one `Examples.BareMetalCounter,
    .one `Examples.Clock, .one `Examples.BareMetalClock,
    .one `Examples.CounterWeb, .one `Examples.DashboardWeb, .one `Examples.TextWeb, .one `Examples.Controls, .one `Examples.ControlsWeb,
    .one `Examples.Phone, .one `Examples.PhoneAndroid, .one `Examples.Sprites]

lean_exe «uvl-demo» where
  root := `Examples.Demo

/-- Reference frames for the bare-metal host test (`baremetal/tools/host_test.sh`). -/
lean_exe «uvl-baremetal-ref» where
  root := `Examples.BareMetalRef

@[test_driver]
lean_exe «uvl-tests» where
  root := `Tests.Main

/-! ## Desktop shell (SDL3)

Only the `uvl-*` window executables need SDL3; the library, demo and tests do
not. SDL3 is located with `pkg-config sdl3` (set `PKG_CONFIG_PATH` if it is
installed in a non-standard prefix). -/

def pkgConfig (args : Array String) : IO (Array String) := do
  try
    let out ← IO.Process.output { cmd := "pkg-config", args }
    if out.exitCode != 0 then return #[]
    return ((out.stdout.replace "\n" " ").splitOn " ").toArray.filter (· != "")
  catch _ => return #[]

/-- wgpu-native: `WGPU_NATIVE_DIR`, or a pinned release fetched into `.lake/wgpu-native`. -/
def wgpuDir (pkgDir : System.FilePath) : IO System.FilePath := do
  if let some d ← IO.getEnv "WGPU_NATIVE_DIR" then return d
  let d := pkgDir / ".lake" / "wgpu-native"
  unless ← (d / "include" / "webgpu" / "webgpu.h").pathExists do
    let out ← IO.Process.output { cmd := (pkgDir / "native" / "fetch_wgpu.sh").toString, args := #[d.toString] }
    if out.exitCode != 0 then
      throw <| IO.userError s!"could not fetch wgpu-native (set WGPU_NATIVE_DIR):\n{out.stderr}"
  return d

def wgpuLibName : String := if System.Platform.isOSX then "libwgpu_native.dylib" else "libwgpu_native.so"

lean_lib UVLWindow

target sdl_shell.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "native" / "sdl_shell.o"
  let srcJob ← inputTextFile <| pkg.dir / "native" / "sdl_shell.c"
  let cflags ← pkgConfig #["--cflags", "sdl3"]
  let weakArgs := #["-I", (← getLeanIncludeDir).toString,
    "-I", ((← wgpuDir pkg.dir) / "include").toString] ++ cflags
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc"

/-- Locate the SDL3 shared library at build time (pkg-config first, then the
usual prefixes). It is passed to the linker directly. -/
def findSDL3 : IO System.FilePath := do
  let names := #["libSDL3.so", "libSDL3.dylib"]
  let fromPC ← pkgConfig #["--variable=libdir", "sdl3"]
  let dirs := fromPC ++ #["/usr/local/lib", "/usr/lib/x86_64-linux-gnu", "/usr/lib/aarch64-linux-gnu",
    "/usr/lib", "/opt/homebrew/lib", "/opt/sdl3/lib"]
  for d in dirs do
    for n in names do
      let p := System.FilePath.mk d / n
      if ← p.pathExists then return p
  throw <| IO.userError "SDL3 not found: install it or set PKG_CONFIG_PATH so `pkg-config sdl3` works"

target sdl3_lib : System.FilePath := do
  return Job.pure (← findSDL3)

/-! ## Desktop GPU renderer (wgpu-native)

`native/gpu_shell.c` draws with wgpu-native's `webgpu.h`. It is taken from
`WGPU_NATIVE_DIR` if set, otherwise a pinned prebuilt release is downloaded
into `.lake/wgpu-native` by `native/fetch_wgpu.sh` on first build. -/

target wgpu_lib pkg : System.FilePath := do
  return Job.pure ((← wgpuDir pkg.dir) / "lib" / wgpuLibName)

target gpu_shell.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "native" / "gpu_shell.o"
  let srcJob ← inputTextFile <| pkg.dir / "native" / "gpu_shell.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString, "-I", ((← wgpuDir pkg.dir) / "include").toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc"

lean_lib UVLGPU

/-- Lean links with its own (older) glibc sysroot; SDL3 and wgpu-native are
built against the system glibc, whose symbols resolve at load time. The rpath
lets executables find wgpu-native where it was found at build time. (macOS has
no separate sysroot: only the rpath is needed.) -/
def nativeLinkArgs : Array String := run_io do
  let dir := (← IO.getEnv "WGPU_NATIVE_DIR").map System.FilePath.mk |>.getD (__dir__ / ".lake" / "wgpu-native")
  let rpath := s!"-Wl,-rpath,{dir / "lib"}"
  return if System.Platform.isOSX then #[rpath] else #["-Wl,--allow-shlib-undefined", rpath]

/-- Renders scenes headless on the GPU and compares them with the CPU. -/
lean_exe «uvl-gpu-check» where
  root := `Examples.GPUCheck
  moreLinkObjs := #[gpu_shell.o, wgpu_lib]
  moreLinkArgs := nativeLinkArgs

lean_exe «uvl-counter» where
  root := `Examples.CounterWindow
  moreLinkObjs := #[sdl_shell.o, gpu_shell.o, sdl3_lib, wgpu_lib]
  moreLinkArgs := nativeLinkArgs

lean_exe «uvl-controls» where
  root := `Examples.ControlsWindow
  moreLinkObjs := #[sdl_shell.o, gpu_shell.o, sdl3_lib, wgpu_lib]
  moreLinkArgs := nativeLinkArgs

/-- A tile map with 300 walking units, camera gestures and an fps counter. -/
lean_exe «uvl-sprites» where
  root := `Examples.SpritesWindow
  moreLinkObjs := #[sdl_shell.o, gpu_shell.o, sdl3_lib, wgpu_lib]
  moreLinkArgs := nativeLinkArgs

lean_exe «uvl-bench» where
  root := `Examples.Bench