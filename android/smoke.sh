#!/usr/bin/env bash
# Smoke test of the Android app on a running emulator or a device (adb):
# install, launch, tap "+", type into the text field, and check that each step
# changes what is on screen and that the app is still alive. Screenshots go to
# $2 (default android/smoke).
#
#   android/smoke.sh [apk] [out-dir]
#
# Needs python3 with Pillow (to compare screenshots).
set -euo pipefail
APK=${1:-android/dist/uvl-example.apk}
OUT=${2:-android/smoke}
PKG=io.github.kidandcat.uvl
mkdir -p "$OUT"

adb install -r "$APK"
adb logcat -c
adb shell am start -W -n "$PKG/android.app.NativeActivity"
sleep 8

shot() { adb exec-out screencap -p > "$OUT/$1.png"; }
alive() {
  if ! adb shell pidof "$PKG" > /dev/null; then
    echo "error: the app is not running ($1)" >&2
    adb logcat -d | grep -E -i "uvl|DEBUG|FATAL|AndroidRuntime|linker" | tail -80 >&2
    exit 1
  fi
}
alive "after launch"
shot launch

# The shell logs its geometry:
#   surface WxH px at D dpi, buffer BWxBH, app LWxLH at (OX, OY)
GEOM=$(adb logcat -d -s uvl:I | grep 'surface' | tail -1)
echo "$GEOM"
read -r PW PH BW BH LW LH OX OY < <(echo "$GEOM" | python3 -c '
import re, sys
m = re.search(r"surface (\d+)x(\d+) px at \d+ dpi, buffer (\d+)x(\d+), app (\d+)x(\d+) at \((\d+), (\d+)\)", sys.stdin.read())
print(*m.groups())')
# a point of the app (logical pixels) on the screen
px() { python3 -c "print(round(($OX + $1) * $PW / $BW))"; }
py() { python3 -c "print(round(($OY + $1) * $PH / $BH))"; }

# Examples/Phone.lean: "+" is 100 px right of the centre, 104 px from the top;
# the text field is 80 px above the bottom.
adb shell input tap "$(px $((LW / 2 + 100)))" "$(py 104)"
sleep 2
alive "after tapping +"
shot tap

adb shell input tap "$(px 150)" "$(py $((LH - 80)))"
sleep 2
adb shell dumpsys input_method | grep -E -o 'mInputShown=[a-z]+' | head -1 || true
adb shell input text "Lean"
adb shell input keyevent 66
sleep 2
alive "after typing"
shot typed

python3 - "$OUT" "$PW" "$PH" "$BW" "$BH" "$OX" "$OY" "$LW" "$LH" <<'PY'
import sys
from PIL import Image, ImageChops
out = sys.argv[1]
pw, ph, bw, bh, ox, oy, lw, lh = map(int, sys.argv[2:])
sx, sy = pw / bw, ph / bh
def region(name, x0, y0, x1, y1):
    """A box of the app (logical pixels) cropped from a screenshot."""
    im = Image.open(f"{out}/{name}.png").convert("RGB")
    return im.crop((round((ox + x0) * sx), round((oy + y0) * sy),
                    round((ox + x1) * sx), round((oy + y1) * sy)))
def changed(a, b, box):
    return ImageChops.difference(region(a, *box), region(b, *box)).getbbox() is not None
counter = (16, 60, lw - 16, 150)
form = (16, lh - 110, lw - 16, lh - 10)
ok = True
for what, a, b, box in [("counter after the tap", "launch", "tap", counter),
                        ("form after typing", "tap", "typed", form)]:
    c = changed(a, b, box)
    print(f"{what}: {'changed' if c else 'UNCHANGED'}")
    ok &= c
# the app drew something: the launch screen is not a single color
colors = region("launch", 0, 0, lw, lh).getcolors(1 << 20)
print(f"launch screen: {len(colors) if colors else 'many'} colors")
ok &= colors is None or len(colors) > 50
sys.exit(0 if ok else 1)
PY
echo "smoke test passed"
