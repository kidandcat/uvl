import Lake
open Lake DSL

package «universal-viz» where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]
  moreLeancArgs := #["-O3"]

@[default_target]
lean_lib UniversalViz

lean_lib Tests where
  globs := #[.one `Tests.PngDecode]

lean_lib Examples where
  globs := #[.one `Examples.Scenes, .one `Examples.Counter]

lean_exe «uviz-demo» where
  root := `Examples.Demo

@[test_driver]
lean_exe «uviz-tests» where
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

lean_lib UVLWindow

target sdl_shell.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "native" / "sdl_shell.o"
  let srcJob ← inputTextFile <| pkg.dir / "native" / "sdl_shell.c"
  let cflags ← pkgConfig #["--cflags", "sdl3"]
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ cflags
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

/-- Lean links with its own (older) glibc sysroot; SDL3 is built against the
system glibc, whose symbols resolve at load time. -/
def sdlLinkArgs : Array String := #["-Wl,--allow-shlib-undefined"]

lean_exe «uvl-counter» where
  root := `Examples.CounterWindow
  moreLinkObjs := #[sdl_shell.o, sdl3_lib]
  moreLinkArgs := sdlLinkArgs

lean_exe «uviz-bench» where
  root := `Examples.Bench
