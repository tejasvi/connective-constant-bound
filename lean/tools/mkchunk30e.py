# mkchunk30e.py PREFIX LO COUNT OUT: 32 seven-bit characters per state (base 128, little endian):
#   8 for n * 2^46 + T (n = cells, T = turn code), 15 for c0 + c1 2^35 + c2 2^70 (child indices, 2^35 - 1 = none),
#   9 for V = floor(v 2^60). The chosen file holds uint32 or uint64 indices (all ones = none), by its size.
#   Prints the character count and the 64-bit FNV-1a hash of the output.
import os, struct, sys
P, lo, cnt, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
N = os.path.getsize(P + ".keys") // 8
W = os.path.getsize(P + ".chosen") // (3 * N)
assert W in (4, 8) and os.path.getsize(P + ".chosen") == 3 * W * N and os.path.getsize(P + ".v") == 8 * N
hi = min(N, lo + cnt)
fk, fc, fv = open(P + ".keys", "rb"), open(P + ".chosen", "rb"), open(P + ".v", "rb")
fk.seek(8 * lo); fc.seek(3 * W * lo); fv.seek(8 * lo)
K = struct.unpack("<%dQ" % (hi - lo), fk.read(8 * (hi - lo)))
C = struct.unpack("<%d%s" % (3 * (hi - lo), "I" if W == 4 else "Q"), fc.read(3 * W * (hi - lo)))
V = struct.unpack("<%dd" % (hi - lo), fv.read(8 * (hi - lo)))
ALL = (1 << (8 * W)) - 1
NONE35 = (1 << 35) - 1
def b128(x, n):
    r = bytearray(n)
    for i in range(n): r[i] = x & 127; x >>= 7
    assert x == 0
    return r
buf = bytearray()
for s in range(hi - lo):
    k = K[s]; m = k >> 58; T = k & ((1 << 58) - 1)
    assert T < (1 << 46) and m < 32
    buf += b128((m << 46) | T, 8)
    cs = []
    for j in range(3):
        c = C[3 * s + j]
        if c == ALL: c = NONE35
        else: assert c < N < NONE35
        cs.append(c)
    buf += b128(cs[0] | (cs[1] << 35) | (cs[2] << 70), 15)
    v = V[s]; assert 0.0 <= v <= 1.0
    buf += b128(int(v * 2.0 ** 60), 9)
open(out, "wb").write(buf)
h = 0xcbf29ce484222325
for x in buf: h = ((h ^ x) * 0x100000001b3) & 0xFFFFFFFFFFFFFFFF
print(len(buf), h)
