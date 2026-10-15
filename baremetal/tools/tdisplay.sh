#!/bin/sh
# Build the bare-metal stopwatch (Examples.BareMetalClock) for a LilyGO
# T-Display and flash it (see "Example: LilyGO T-Display" in baremetal/README.md):
#
#   1. build the Lean code and bundle the app's C with uvl_rt.c; on hosts
#      without GNU ld (macOS) the bundling runs in the `uvl-bundler` image
#      (baremetal/tools/Dockerfile);
#   2. build the ESP-IDF project with the T-Display board selected;
#   3. flash it at 460800 baud and, with --monitor, open the serial monitor.
#
# Usage: baremetal/tools/tdisplay.sh [--monitor] [port]
#   port    serial port (default: the first /dev/cu.usbserial-* or /dev/ttyUSB*)
#   UVL_ENTRY=Examples.BareMetalCounter selects another exported app.
# Needs ESP-IDF's environment (`. $IDF_PATH/export.sh`) and `lake` on PATH.
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
OUT=${UVL_BAREMETAL_DIR:-$ROOT/.lake/baremetal}
ENTRY=${UVL_ENTRY:-Examples.BareMetalClock}
MONITOR=
if [ "${1:-}" = "--monitor" ]; then MONITOR=monitor; shift; fi
PORT=${1:-$(ls /dev/cu.usbserial-* /dev/ttyUSB* 2>/dev/null | head -1)}
[ -n "$PORT" ] || { echo "no serial port found; pass one" >&2; exit 1; }
command -v idf.py >/dev/null || { echo "load ESP-IDF first: . \$IDF_PATH/export.sh" >&2; exit 1; }
cd "$ROOT"
mkdir -p "$OUT"
B="$OUT/bundle-tdisplay"

echo "== building Lean"
lake build Examples
bundle='set -e
L=$(lean --print-prefix)
[ -s "$0/init-c/Init.Prelude.c" ] || baremetal/tools/gen_init_c.sh "$L" "$0/init-c"
python3 baremetal/tools/uvl_bundle.py --entry "$1" --lean-prefix "$L" --ir .lake/build/ir \
  --init-c "$0/init-c" --out "$2"'
echo "== bundling $ENTRY"
if [ "$(uname)" = Darwin ]; then
  docker image inspect uvl-bundler >/dev/null 2>&1 ||
    docker build -t uvl-bundler "$HERE"
  # Paths are mounted 1:1, so OUT must be under a directory Docker shares (e.g. $HOME).
  docker run --rm -v "$ROOT:$ROOT" -v "$OUT:$OUT" -w "$ROOT" uvl-bundler \
    sh -c "$bundle" "$OUT" "$ENTRY" "$B" >"$OUT/bundle-tdisplay.log" 2>&1
else
  sh -c "$bundle" "$OUT" "$ENTRY" "$B" >"$OUT/bundle-tdisplay.log" 2>&1
fi || { tail -20 "$OUT/bundle-tdisplay.log"; exit 1; }
tail -1 "$OUT/bundle-tdisplay.log"

echo "== building firmware"
export UVL_BUNDLE="$B"
P="$OUT/esp-tdisplay"
mkdir -p "$P"
# Keep the build directory between runs; a stale sdkconfig would keep the old board.
rsync -a --delete --exclude build --exclude sdkconfig "$ROOT/baremetal/esp-idf/" "$P/"
cd "$P"
[ -f sdkconfig ] && grep -q '^CONFIG_UVL_BOARD_TDISPLAY=y' sdkconfig || {
  rm -f sdkconfig
  idf.py -DSDKCONFIG_DEFAULTS="sdkconfig.defaults;boards/t-display.defaults" set-target esp32 \
    >"$OUT/esp-tdisplay.log" 2>&1 || { tail -20 "$OUT/esp-tdisplay.log"; exit 1; }
}
idf.py -DUVL_BUNDLE="$B" build >>"$OUT/esp-tdisplay.log" 2>&1 ||
  { tail -30 "$OUT/esp-tdisplay.log"; exit 1; }

echo "== flashing $PORT"
# The board's WCH USB-serial bridge fails at idf.py's default 921600 baud.
exec idf.py -DUVL_BUNDLE="$B" -p "$PORT" -b 460800 flash $MONITOR
