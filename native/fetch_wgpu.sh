#!/usr/bin/env bash
# Download a prebuilt wgpu-native (the WebGPU implementation used by the
# desktop GPU renderer, native/gpu_shell.c) into $1 (default .lake/wgpu-native).
# The lakefile runs this on first build unless WGPU_NATIVE_DIR points to an
# existing installation (with include/webgpu/webgpu.h and lib/).
# WGPU_NATIVE_ASSET picks another platform's build (android/build.sh fetches
# wgpu-android-<arch>-release.zip).
set -euo pipefail
VERSION=${WGPU_NATIVE_VERSION:-v27.0.4.0}
DEST=${1:-$(cd "$(dirname "$0")/.." && pwd)/.lake/wgpu-native}
ASSET=${WGPU_NATIVE_ASSET:-}
[ -n "$ASSET" ] || case "$(uname -s)-$(uname -m)" in
  Linux-x86_64) ASSET=wgpu-linux-x86_64-release.zip ;;
  Linux-aarch64) ASSET=wgpu-linux-aarch64-release.zip ;;
  Darwin-arm64) ASSET=wgpu-macos-aarch64-release.zip ;;
  Darwin-x86_64) ASSET=wgpu-macos-x86_64-release.zip ;;
  *) echo "fetch_wgpu.sh: no prebuilt wgpu-native for $(uname -sm)" >&2; exit 1 ;;
esac
if [ -f "$DEST/include/webgpu/webgpu.h" ]; then exit 0; fi
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
echo "fetching wgpu-native $VERSION ($ASSET)" >&2
curl -fsSL -o "$TMP/wgpu.zip" "https://github.com/gfx-rs/wgpu-native/releases/download/$VERSION/$ASSET"
mkdir -p "$DEST"
unzip -q -o "$TMP/wgpu.zip" -d "$DEST"
