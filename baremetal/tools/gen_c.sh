#!/bin/sh
# gen_c.sh <lean-prefix> <out-dir> <Module/Path.lean>...
#
# Emit C for modules of Lean's own libraries (Init, Std, Lean) with the
# installed compiler. The toolchain ships these libraries only as host object
# code; a microcontroller build needs their C. Paths are relative to
# <lean-prefix>/src/lean. Runs in parallel; existing outputs are kept.
set -e
L=$1; OUT=$2; shift 2
mkdir -p "$OUT"
OUT=$(cd "$OUT" && pwd)
if [ "$1" = "--one" ]; then
  f=$2
  m=$(echo "${f%.lean}" | tr / .)
  [ -s "$OUT/$m.c" ] && exit 0
  cd "$L/src/lean"
  if LEAN_PATH="$L/lib/lean" "$L/bin/lean" --root="$L/src/lean" -c "$OUT/$m.c.tmp" "$f" >/dev/null; then
    mv "$OUT/$m.c.tmp" "$OUT/$m.c"
  else
    echo "gen_c: failed on $f" >&2; exit 1
  fi
  exit 0
fi
printf '%s\n' "$@" | xargs -P "$(nproc 2>/dev/null || echo 4)" -n 1 "$0" "$L" "$OUT" --one
