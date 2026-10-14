#!/bin/sh
# Bare-metal pipeline test (see baremetal/README.md):
#
#   1. bundle the counter app's generated C with uvl_rt.c (no libleanrt);
#   2. run the bundle on the host (64-bit, then 32-bit if `gcc -m32` works);
#   3. cross-compile it for ARM Cortex-M3 and run it under QEMU (if
#      arm-none-eabi-gcc and qemu-system-arm are installed);
#
# and check that every build streams frames byte-identical (RGB565) to the
# native Lean build of the same exported functions.
#
# Usage: baremetal/tools/test.sh   (from anywhere; uses `lake` and `lean` on PATH)
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
cd "$ROOT"
L=$(lean --print-prefix)
OUT=${UVL_BAREMETAL_DIR:-$ROOT/.lake/baremetal}
mkdir -p "$OUT"

lake build Examples uvl-baremetal-ref
if [ ! -s "$OUT/init-c/Init.Prelude.c" ]; then
  echo "== generating C for Lean's Init library (once per toolchain)"
  "$HERE/gen_init_c.sh" "$L" "$OUT/init-c"
fi
echo "== bundling"
python3 "$HERE/uvl_bundle.py" --lean-prefix "$L" --ir .lake/build/ir --init-c "$OUT/init-c" \
  --out "$OUT/bundle" 2>"$OUT/bundle.log"
grep -v 'removing unused' "$OUT/bundle.log" >&2 || true

mkdir -p "$OUT/ref" "$OUT/host64" "$OUT/host32" "$OUT/qemu"
.lake/build/bin/uvl-baremetal-ref "$OUT/ref"

same() {
  cmp -s "$OUT/ref/frame0.rgb565" "$1/frame0.rgb565" && cmp -s "$OUT/ref/frame1.rgb565" "$1/frame1.rgb565"
}
fail=0
B=$OUT/bundle
CFLAGS="-O2 -w -ffunction-sections -fdata-sections -I$B/include"

echo "== host, 64-bit"
"$B/uvl-host" "$OUT/host64" 20
if same "$OUT/host64"; then echo "[ok] 64-bit frames identical to native Lean"; else echo "[FAIL] 64-bit frames differ"; fail=1; fi

if echo 'int main(void){return 0;}' | cc -m32 -x c - -o "$OUT/m32probe" 2>/dev/null; then
  echo "== host, 32-bit"
  cc -m32 -msse2 -mfpmath=sse $CFLAGS -DUVL_HEAP_SIZE=98304 "$B"/src/*.c "$B"/rt/*.c "$ROOT/baremetal/host/main.c" \
    -Wl,--gc-sections -lm -o "$OUT/uvl-host32"
  "$OUT/uvl-host32" "$OUT/host32" 20
  if same "$OUT/host32"; then echo "[ok] 32-bit frames identical (96 KB pool)"; else echo "[FAIL] 32-bit frames differ"; fail=1; fi
else
  echo "-- skipping 32-bit host run (no multilib gcc)"
fi

if command -v arm-none-eabi-gcc >/dev/null && command -v qemu-system-arm >/dev/null; then
  echo "== ARM Cortex-M3 under QEMU (mps2-an385, semihosting)"
  arm-none-eabi-gcc -mcpu=cortex-m3 -mthumb $CFLAGS -DUVL_HEAP_SIZE=98304 "$B"/src/*.c "$B"/rt/*.c \
    "$ROOT/baremetal/host/main.c" "$ROOT/baremetal/qemu/startup.c" -T "$ROOT/baremetal/qemu/mps2.ld" \
    --specs=rdimon.specs -Wl,--gc-sections -lm -o "$OUT/uvl-m3.elf"
  arm-none-eabi-size "$OUT/uvl-m3.elf"
  (cd "$OUT/qemu" && timeout 600 qemu-system-arm -M mps2-an385 -nographic \
    -semihosting-config enable=on,target=native,arg=uvl,arg=.,arg=0 -kernel "$OUT/uvl-m3.elf")
  if same "$OUT/qemu"; then echo "[ok] ARM frames identical"; else echo "[FAIL] ARM frames differ"; fail=1; fi
else
  echo "-- skipping ARM/QEMU run (needs arm-none-eabi-gcc and qemu-system-arm)"
fi
exit $fail
