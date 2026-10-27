# chk_pack30e_v1.py KEYS CHOSEN V LO CNT BIN: independent check of one pack30e_v1 output (test tool).
# Decodes every record of BIN with the field layout of K30B.recOf30 / recAt30 and compares it with the inputs read
# directly (mkchunk30e.py semantics: all-ones child -> 2^35 - 1, V = int(v * 2^60)); checks the padding is zero.
import os, struct, sys

kf, cf, vf, lo, cnt, bf = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
N = os.path.getsize(kf) // 8
NONE35, M35 = (1 << 35) - 1, (1 << 35) - 1
with open(kf, "rb") as f:
    f.seek(8 * lo); K = struct.unpack("<%dQ" % cnt, f.read(8 * cnt))
with open(cf, "rb") as f:
    f.seek(24 * lo); C = struct.unpack("<%dQ" % (3 * cnt), f.read(24 * cnt))
with open(vf, "rb") as f:
    f.seek(8 * lo); V = struct.unpack("<%dd" % cnt, f.read(8 * cnt))
b = open(bf, "rb").read()
nleaf = (cnt + 63) // 64
assert len(b) == nleaf * 64 * 28, (len(b), nleaf)
bad = 0
for j in range(cnt):
    x = int.from_bytes(b[28 * j:28 * j + 28], "little")
    n, T, c0, c1, c2, W = (x & 63, (x >> 6) & ((1 << 48) - 1), (x >> 54) & M35, (x >> 89) & M35, (x >> 124) & M35,
                           (x >> 159) & ((1 << 61) - 1))
    k = K[j]
    cs = [NONE35 if c == (1 << 64) - 1 else c for c in C[3 * j:3 * j + 3]]
    exp = (k >> 58, k & ((1 << 58) - 1), cs[0], cs[1], cs[2], int(V[j] * 2.0 ** 60))
    if (n, T, c0, c1, c2, W) != exp or x >> 220 != 0 or not all(c == NONE35 or c < N for c in cs):
        bad += 1
        if bad <= 5:
            print("MISMATCH state", lo + j, (n, T, c0, c1, c2, W), exp)
pad = b[28 * cnt:]
print("records", cnt, "mismatches", bad, "padding bytes", len(pad), "nonzero padding", sum(1 for z in pad if z))
sys.exit(1 if bad or any(pad) else 0)
