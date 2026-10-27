# gen_bttest_v1.py KEYS CHOSEN V OUTDIR M NREC: Lean test of the K30E data layout (test tool).
# Writes OUTDIR/K30Test/D.lean (module M of the export as K30EData would hold it: bt_bin% of ../data/m%05d.bin) and
# OUTDIR/K30Test/Chk.lean: for chosen records (first, last, leaf edges, random), kernel checks that rdT30 (module at
# index 0 of a one-module table, local index) and rdKr (the shard path, global index) give the fields read directly
# from the certificate inputs (mkchunk30e.py semantics), plus one deliberately wrong value that must fail (in Neg.lean).
import os, random, struct, sys

kf, cf, vf, out, M, NREC = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5]), int(sys.argv[6])
R = 1 << 20
lo = M * R
nleaf = (NREC + 63) // 64
NONE35 = (1 << 35) - 1

def rec(i):
    with open(kf, "rb") as f:
        f.seek(8 * i); k = struct.unpack("<Q", f.read(8))[0]
    with open(cf, "rb") as f:
        f.seek(24 * i); cs = struct.unpack("<3Q", f.read(24))
    with open(vf, "rb") as f:
        f.seek(8 * i); v = struct.unpack("<d", f.read(8))[0]
    cs = [NONE35 if c == (1 << 64) - 1 else c for c in cs]
    return (k >> 58, k & ((1 << 58) - 1), cs[0], cs[1], cs[2], int(v * 2.0 ** 60))

rnd = random.Random(20261025 + M)
idx = sorted(set([0, 1, 62, 63, 64, 65, 127, 128, NREC // 2, NREC - 2, NREC - 1] + [rnd.randrange(NREC) for _ in range(24)]))
os.makedirs(os.path.join(out, "K30Test"), exist_ok=True)
open(os.path.join(out, "K30Test", "D.lean"), "w").write(
    "import Saw38aK.LitBin\n\nnamespace K30Test\n\nopen Saw38aK\n\nset_option maxHeartbeats 0 in\n"
    "noncomputable def M%05d : BT Nat := bt_bin%% \"../data/m%05d.bin\" %d 1792\n\nend K30Test\n" % (M, M, nleaf))
def fields(e, r):
    return " && ".join("Nat.beq (%s).%s %d" % (e, f, x) for f, x in zip(["n", "T", "c0", "c1", "c2", "V"], r))
L = ["import K30B.Look", "import K30Test.D", "", "namespace K30Test", "", "open Saw38aCore Saw38aK K30B", "",
     "set_option maxRecDepth 100000", ""]
for j in idx:
    r = rec(lo + j)
    L.append("theorem t%d : (%s) = true := by decide +kernel" % (j, fields("rdT30 (.node M%05d .leaf .leaf) 64 16384 %d" % (M, j), r)))
    L.append("theorem k%d : (%s) = true := by decide +kernel" % (j, fields("rdKr [(%d, M%05d)] %d" % (M, M, lo + j), r)))
L += ["", "end K30Test", ""]
open(os.path.join(out, "K30Test", "Chk.lean"), "w").write("\n".join(L))
j = idx[len(idx) // 2]
r = list(rec(lo + j)); r[5] += 1
open(os.path.join(out, "K30Test", "Neg.lean"), "w").write("\n".join(
    ["import K30B.Look", "import K30Test.D", "", "namespace K30Test", "", "open Saw38aCore Saw38aK K30B", "",
     "theorem neg : (%s) = true := by decide +kernel" % fields("rdKr [(%d, M%05d)] %d" % (M, M, lo + j), r), "",
     "end K30Test", ""]))
print("records checked", len(idx), "module", M, "leaves", nleaf)
