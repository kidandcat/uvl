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
  globs := #[.one `Examples.Scenes]

lean_exe «uviz-demo» where
  root := `Examples.Demo

@[test_driver]
lean_exe «uviz-tests» where
  root := `Tests.Main
