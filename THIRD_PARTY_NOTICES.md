# Third-party notices

UVL itself is under the MIT license in [LICENSE](LICENSE) (copyright line
matches [kidandcat/cairn](https://github.com/kidandcat/cairn/blob/main/LICENSE)
and [kidandcat/vos](https://github.com/kidandcat/vos/blob/main/LICENSE)).
This file lists code and assets that are not under that license, or that are
fetched when you build and are not stored in this repository.

The 5×7 bitmap font (`UVL/Render/glyph_table.c`, `UVL/Render/Font.lean`) and
the PNG fixtures under `Tests/` have no separate upstream notice. They are
part of this repository and covered by [LICENSE](LICENSE). The fixtures are
produced by `Tests/fixtures/mkpng.py` and the demo.

## In this repository

### UVL Sans (SIL Open Font License 1.1)

`assets/fonts/UVLSans-Regular.ttf`, and the same bytes embedded by
`tools/embed_font.py` into `UVL/Text/UVLSansData.lean`.

UVL Sans is a subset of Liberation Sans Regular with hinting removed and the
font renamed. The reserved font names are Liberation and Arimo; the renamed
font does not use them. The font's name table still carries:

- Digitized data copyright (c) 2010 Google Corporation.
- Copyright (c) 2012 Red Hat, Inc.

The full SIL Open Font License 1.1 is in [assets/fonts/OFL.txt](assets/fonts/OFL.txt).
The OFL is not the MIT license: the font and its derivatives stay under the
OFL, and that requirement does not apply to documents rendered with the font.

## Fetched at build time (not committed)

These are not in git. Versions are the ones the scripts and CI pin today.

### wgpu-native v27.0.4.0

`native/fetch_wgpu.sh` downloads a prebuilt archive from
`gfx-rs/wgpu-native` (desktop and Android GPU shells). The crate at tag
`v27.0.4.0` declares `license = "MIT OR Apache-2.0"` in `Cargo.toml`, with
`LICENSE.MIT` (Copyright (c) 2021 The gfx-rs developers) and `LICENSE.APACHE`
in the source repository.

The Linux release zip `wgpu-linux-x86_64-release.zip` for that tag was
unpacked for this notice. It contains `include/webgpu/webgpu.h`,
`include/webgpu/wgpu.h`, `lib/libwgpu_native.so`, `lib/libwgpu_native.a`, and
a small `wgpu-native-meta/` directory. It does **not** contain `LICENSE`,
`NOTICE`, or any other license file, and `libwgpu_native.so` has no embedded
copyright or SPDX strings. See [Unclear](#unclear) for what that leaves open.

`include/webgpu/webgpu.h` inside that zip starts with:

```
Copyright 2019-2023 WebGPU-Native developers
SPDX-License-Identifier: BSD-3-Clause
```

`include/webgpu/wgpu.h` in the same zip has no license header.

### libuv v1.48.0

`android/build.sh` clones this tag into the Lake cache and links it into the
Android `libuvl.so`. Not committed. The tag's `LICENSE` is the MIT license,
Copyright (c) 2015-present libuv project contributors.

### Lean 4 v4.35.0

Pinned in `lean-toolchain`. The web and Android scripts clone the matching
runtime sources (`src/runtime`, `src/include`, `src/util`) into the Lake cache
and compile `Init` from the toolchain tree. Those sources are not committed.
Source files in that tag are marked as released under the Apache License 2.0
(see the headers in `leanprover/lean4` and the repository `LICENSE`).

### SDL 3.2.24

Desktop window executables link SDL3 found on the system (`pkg-config sdl3`).
CI builds the official tarball `SDL3-3.2.24.tar.gz`. SDL is not committed.
`LICENSE.txt` at tag `release-3.2.24` is the zlib license, Copyright (C)
1997-2025 Sam Lantinga.

### Emscripten

`web/build.sh` needs an Emscripten SDK on `PATH`. CI installs emsdk
`6.0.12`. Emscripten is not committed. The `LICENSE` file in
`emscripten-core/emscripten` (read from the default branch, not diffed
against the 6.0.12 tag) offers the MIT license and the University of
Illinois/NCSA Open Source License. That file also points at bundled musl
(MIT) and a `third_party/` tree that is not used by a default UVL browser
build.

### Android NDK `native_app_glue`

`android/build.sh` compiles
`$NDK/sources/android/native_app_glue/android_native_app_glue.c` from the NDK
the builder has installed (r26 or newer). The glue sources are not copied
into this repository. See [Unclear](#unclear).

## Unclear

These were inspected far enough to see that a license could not be stated
from a notice in the artifact. They are not assigned a license here.

1. **Transitive licenses inside the wgpu-native prebuilt libraries.**
   `libwgpu_native.so` and `libwgpu_native.a` in the v27.0.4.0 release zip
   ship no `NOTICE` and no per-crate license texts. The wgpu-native crate
   itself is MIT OR Apache-2.0, but the static library links other Rust
   crates. Those crate licenses were not enumerated. Anyone redistributing
   the prebuilt library needs to collect them from the wgpu-native lockfile
   at tag `v27.0.4.0` (and from the native libraries that build enables,
   such as Vulkan or Metal loaders).

2. **`include/webgpu/wgpu.h` in that same zip** has no copyright or SPDX
   header. It is part of the wgpu-native release, whose crate license is
   MIT OR Apache-2.0, but the header does not say so itself.

3. **`android_native_app_glue`.** The NDK path above is compiled at APK
   build time. The header was not read from an NDK checkout while preparing
   this file, so this notice does not name its license. Read the copyright
   banner in the NDK you install before redistributing an APK that links it.
