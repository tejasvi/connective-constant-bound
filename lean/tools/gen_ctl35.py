#!/usr/bin/env python3
"""gen_ctl35.py PREFIX OUT: native controls of the k30e checker for the two high bits of its 35-bit child indices
(positive and negative). For bit 33 (children in [2^33, 2^34), states from 2^33) and bit 34 (children at least 2^34,
states from 2^34), and for each slot t = 0, 1, 2: the decoded child index of the first such state must equal the
uint64 value in the certificate file, and must differ from that value without the bit. A window of 1000 states from
index 2^34 must pass, and must fail with N = 2^34 (children above 2^34 out of range) and with a misaligned record
layout (chunk size + 1)."""
import os, struct, sys
P, OUT = sys.argv[1], sys.argv[2]
N = os.path.getsize(P + ".keys") // 8
W = os.path.getsize(P + ".chosen") // (3 * N); assert W == 8
NONE = (1 << 64) - 1
f = open(P + ".chosen", "rb")
def children(lo, cnt):
    f.seek(24 * lo)
    return struct.unpack("<%dQ" % (3 * cnt), f.read(24 * cnt))
LO = 1 << 34
C = children(LO, 1000)
assert any(c != NONE and c >= LO for c in C), "no child above 2^34 in the window"
picks = []
for b in (33, 34):
    C = children(1 << b, 100000)
    for t in range(3):
        for s in range(100000):
            c = C[3 * s + t]
            if c != NONE and (1 << b) <= c < (1 << (b + 1)):
                picks.append((b, (1 << b) + s, t, c)); break
        else:
            raise SystemExit("no slot-%d child with bit %d found" % (t, b))
NUM, DEN = 105432502045487, 39656386815908
L = [f"""import Saw38aCore
import L38Data.All

/-! Native controls for the high bits of the 35-bit child indices (k30e). -/

namespace L38.Ctl35

/-- Positive: the 1000 states from index 2^34 pass the check. -/
theorem window_ok : Saw38aCore.checkRange L38.Data.chunks L38.Data.chunkStates L38.Data.numStates {NUM} {DEN}
    {LO} {LO + 1000} = true := by native_decide
"""]
for b, i, t, v in picks:
    fld = ["c0", "c1", "c2"][t]
    L.append(f"""
/-- Positive: state {i} has child index {v} (bit {b} set) in slot {t}, as in the certificate file. -/
theorem child_ok_b{b}_s{t} : (Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates {i}).{fld} = {v} := by
  native_decide

/-- Negative: without bit {b} the same child index would be {v - (1 << b)}; it is not. -/
theorem child_no_b{b}_s{t} :
    decide ((Saw38aCore.readRec L38.Data.chunks L38.Data.chunkStates {i}).{fld} = {v - (1 << b)}) = false := by
  native_decide
""")
L.append(f"""
/-- Negative: with N = 2^34 the window fails (children above 2^34 are out of range). -/
theorem window_bound_fails : Saw38aCore.checkRange L38.Data.chunks L38.Data.chunkStates {LO} {NUM} {DEN}
    {LO} {LO + 1000} = false := by native_decide

/-- Negative: with a misaligned record layout (chunk size + 1) the window fails. -/
theorem window_misaligned_fails : Saw38aCore.checkRange L38.Data.chunks (L38.Data.chunkStates + 1) L38.Data.numStates
    {NUM} {DEN} {LO} {LO + 1000} = false := by native_decide

end L38.Ctl35
""")
open(OUT, "w").write("".join(L))
print("; ".join("bit %d state %d slot %d child %d" % p for p in picks))
