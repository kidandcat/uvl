#!/bin/sh
# gen_init_c.sh <lean-prefix> <out-dir>: C for every module of Lean's `Init`
# library (about 650 files, a few minutes; done once per toolchain).
set -e
L=$1; OUT=$2
cd "$L/src/lean"
exec "$(dirname "$0")/gen_c.sh" "$L" "$OUT" Init.lean $(find Init -name '*.lean')
