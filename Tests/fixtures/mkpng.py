import zlib, struct, sys, os
# Regenerate the PNG decoder fixtures: python3 Tests/fixtures/mkpng.py Tests/fixtures
W, H = 24, 17
def chunk(t, b): return struct.pack('>I', len(b)) + t + b + struct.pack('>I', zlib.crc32(t + b) & 0xffffffff)
def paeth(a, b, c):
    p = a + b - c; pa, pb, pc = abs(p - a), abs(p - b), abs(p - c)
    return a if pa <= pb and pa <= pc else (b if pb <= pc else c)
def png(ctype, bpp, pix, level, extra=b''):
    stride = W * bpp; raw = bytearray(); prev = bytes(stride)
    for y in range(H):
        row = pix[y*stride:(y+1)*stride]; f = y % 5; raw.append(f)
        for x in range(stride):
            a = row[x-bpp] if x >= bpp else 0; b = prev[x]; c = prev[x-bpp] if x >= bpp else 0
            pred = [0, a, b, (a+b)//2, paeth(a, b, c)][f]
            raw.append((row[x] - pred) & 255)
        prev = row
    z = zlib.compress(bytes(raw), level)
    print(ctype, 'level', level, 'btype', (z[2] >> 1) & 3, file=sys.stderr)
    ihdr = struct.pack('>IIBBBBB', W, H, 8, ctype, 0, 0, 0)
    return b'\x89PNG\r\n\x1a\n' + chunk(b'IHDR', ihdr) + extra + chunk(b'IDAT', z[:len(z)//2]) + chunk(b'IDAT', z[len(z)//2:]) + chunk(b'IEND', b'')
R = lambda x, y: (x*11) % 256; G = lambda x, y: (y*15) % 256; B = lambda x, y: ((x+y)*7) % 256
P = [(x, y) for y in range(H) for x in range(W)]
out = sys.argv[1]
w = lambda n, d: open(os.path.join(out, n), 'wb').write(d)
w('rgba.png', png(6, 4, bytes(v for x, y in P for v in (R(x,y), G(x,y), B(x,y), (x*y*3) % 256)), 9))
w('rgb.png', png(2, 3, bytes(v for x, y in P for v in (R(x,y), G(x,y), B(x,y))), 0))
w('gray.png', png(0, 1, bytes(R(x,y) for x, y in P), 6))
w('graya.png', png(4, 2, bytes(v for x, y in P for v in (R(x,y), G(x,y))), 9))
pal = bytes(v for k in range(16) for v in (k*16, 255-k*16, k*7))
trns = bytes(k*30 for k in range(8))
w('palette.png', png(3, 1, bytes((x+y) % 16 for x, y in P), 9, chunk(b'PLTE', pal) + chunk(b'tRNS', trns)))
