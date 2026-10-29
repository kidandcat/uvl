# Contributing

Issues and pull requests are welcome. By participating you agree to the
[Code of Conduct](CODE_OF_CONDUCT.md). Report security problems the way
[SECURITY.md](SECURITY.md) describes, not in a public issue.

## What you need

Lean `v4.35.0`, pinned in `lean-toolchain`. [elan](https://github.com/leanprover/elan)
installs that toolchain when you run `lake` in this directory.

```sh
lake build
lake test
lake exe uvl-demo
lake exe uvl-bench
```

That is the library job in [`.github/workflows/ci.yml`](.github/workflows/ci.yml).
Windowed apps also need SDL3 (`pkg-config sdl3`). The GPU shells download a
pinned wgpu-native on first build unless `WGPU_NATIVE_DIR` is set. The browser
build needs an Emscripten SDK (`web/build.sh`). The Android APK needs the NDK
and SDK (`android/build.sh`). Bare metal is described in
[baremetal/README.md](baremetal/README.md).

`scripts/check-version.sh` must pass. It checks that `version := v!"X.Y.Z"` in
`lakefile.lean` matches the top numbered heading in `CHANGELOG.md`.

## Changes

Match the style of the file you edit. Comments, docstrings, error strings,
log lines, scripts, and docs are in English. Non-ASCII characters in tests
and examples are often Unicode coverage data (accents, CJK, punctuation such
as `¡`); leave those strings alone unless you are changing the test on
purpose. If a golden image or snapshot depends on a string you change, update
it in the same commit and show that `lake test` passes.

User-visible work gets an entry under `## [Unreleased]` in
[CHANGELOG.md](CHANGELOG.md). A version bump follows
[RELEASING.md](RELEASING.md) and is done by a maintainer when cutting a
release, not in an ordinary pull request.

This repository has no contributor license agreement. Contributions are
under the [MIT license](LICENSE), the same as the rest of the project.
The bundled font stays under the SIL Open Font License; see
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
