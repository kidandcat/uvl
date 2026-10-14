#!/usr/bin/env python3
"""Build assets/fonts/UVLSans-Regular.ttf, the default TrueType font of UVL.

A subset of Liberation Sans Regular (SIL Open Font License 1.1) with Latin-1
and common punctuation, no hinting, renamed "UVL Sans" as the OFL requires for
modified versions (the reserved names are "Liberation", "Arimo").

  pip install fonttools
  tools/subset_font.py /usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf
"""
import sys
from pathlib import Path
from fontTools import subset
from fontTools.ttLib import TTFont

src = sys.argv[1]
out = Path(__file__).resolve().parent.parent / "assets" / "fonts" / "UVLSans-Regular.ttf"
opts = subset.Options()
opts.hinting = False
opts.layout_features = ["kern"]
opts.drop_tables += ["DSIG", "GPOS", "GSUB", "GDEF", "FFTM", "gasp", "prep", "fpgm", "cvt "]
opts.name_IDs = [0, 1, 2, 3, 4, 5, 6]
opts.legacy_kern = True
font = TTFont(src)
unicodes = list(range(0x20, 0x7F)) + list(range(0xA0, 0x100)) + [
    0x2013, 0x2014, 0x2018, 0x2019, 0x201C, 0x201D, 0x2022, 0x2026, 0x20AC, 0x2212]
sub = subset.Subsetter(opts)
sub.populate(unicodes=unicodes)
sub.subset(font)
names = font["name"]
for rec in names.names:
    s = rec.toUnicode()
    if rec.nameID in (1, 16):
        rec.string = "UVL Sans"
    elif rec.nameID == 3:
        rec.string = "UVL Sans Regular (subset of Liberation Sans)"
    elif rec.nameID == 4:
        rec.string = "UVL Sans Regular"
    elif rec.nameID == 6:
        rec.string = "UVLSans-Regular"
    else:
        rec.string = s
font.save(out)
print(out, out.stat().st_size, "bytes")
