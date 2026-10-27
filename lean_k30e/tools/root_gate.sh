#!/bin/bash
# root_gate.sh STAGE: the root module and the statement check, after the 3,889 parts are built (build_part.sh).
#   STAGE = gen (part list + root source) | build (gen + root build + #print axioms) | gate (build + statement check).
# Environment:
#   LEAN, MATHLIB_PKGS            as for build_proof.sh;
#   K30E_LIB, K30E_PROOF          the outputs of build_lib.sh and build_proof.sh;
#   K30E_DATAPUB                  public .olean files of the data modules (K30EData/*.olean);
#   K30E_M0                       a directory with K30EData/M00000.olean, .olean.server and .olean.private (the root
#                                 reads the start record with `import all`);
#   K30E_ASM                      work directory: lists/units_partNNNN.txt (gen_partlists_v1.awk) and
#                                 build/K30EP/PNNNN.olean* (build_part.sh); outputs go to K30E_ASM/root;
#   K30E_FROZEN                   the statement check's frozen side: a directory with SHA256SUMS, Saw38a/Spec.lean and
#                                 Saw38a/Statements30e.lean of ../lean, and build/ from build_frozen.sh;
#   K30E_COPY                     the module copy of the statement file (src/Saw38a/Statements30e.lean).
set -eu
STAGE=${1:?gen|build|gate}
T=$(cd "$(dirname "$0")" && pwd)
LEAN=${LEAN:-lean}; P=${MATHLIB_PKGS:?}; LIB=${K30E_LIB:?}; PRF=${K30E_PROOF:?}; DP=${K30E_DATAPUB:?}; M0=${K30E_M0:?}
A=${K30E_ASM:?}; R=$A/root
MP=""
for d in mathlib batteries aesop Qq proofwidgets importGraph LeanSearchClient plausible Cli; do MP=$MP:$P/$d/.lake/build/lib/lean; done
mkdir -p "$R/src/K30ER" "$R/build/K30ER" "$R/gate"
for p in $(seq 0 3888); do q=$(printf %04d $p); awk -v n=K30EP.P$q 'NR==1{lo=$2} {c+=$3} END{print n, lo, c}' "$A/lists/units_part$q.txt"; done > "$R/parts.txt"
awk 'NR==1 && $2!=0 {bad=1} NR>1 && $2!=e {bad=1} {e=$2+$3} END{if (bad) {print "part list not contiguous"; exit 1} print "part list contiguous 0 ..", e}' "$R/parts.txt"
python3 "$T/gen_asm.py" root K30EK K30EData K30EData.Top K30EData.Params K30EData.M00000 "$R/parts.txt" 30 \
  105432502045487 39656386815908 2.6586513 "$R/src/K30ER/Final.lean"
sha256sum "$R/parts.txt" "$R/src/K30ER/Final.lean"
[ "$STAGE" = gen ] && exit 0
miss=0; for p in $(seq 0 3888); do q=$(printf %04d $p); for e in olean olean.server olean.private; do [ -s "$A/build/K30EP/P$q.$e" ] || miss=$((miss+1)); done; done
[ $miss -eq 0 ] || { echo "missing part files: $miss"; exit 3; }
python3 "$T/gen_setup_v2.py" K30EP.BASE "$R/base_setup.json" "$LIB" "$DP"
python3 "$T/gen_setup_v4.py" K30ER.Final "$R/setup_root.json" "$R/base_setup.json" --full "$M0" "$A/build"
export LEAN_PATH=$PRF:$LIB$MP
python3 "$T/rtime.py" "$LEAN" --setup "$R/setup_root.json" -DElab.async=false -j1 -o "$R/build/K30ER/Final.olean" "$R/src/K30ER/Final.lean"
for e in olean olean.server olean.private; do [ -s "$R/build/K30ER/Final.$e" ] || { echo "root file $e missing"; exit 4; }; done
sha256sum "$R/build/K30ER/Final.olean" "$R/build/K30ER/Final.olean.server" "$R/build/K30ER/Final.olean.private"
printf 'module\npublic import K30ER.Final\n#print axioms Saw38a.K30EK.cert_exists\n#print axioms Saw38a.K30EK.bridge_bound\n#print axioms Saw38a.K30EK.connective_constant_le\n#print axioms Saw38a.K30EK.connective_constant_le_unconditional\n' > "$R/chk_root.lean"
python3 "$T/gen_setup_v4.py" ChkRoot "$R/setup_chk_root.json" "$R/setup_root.json" "$R/build"
python3 "$T/rtime.py" "$LEAN" --setup "$R/setup_chk_root.json" -j1 "$R/chk_root.lean"
[ "$STAGE" = build ] && exit 0
rc=0
python3 "$T/gen_setup_v4.py" AxgateCheckK "$R/setup_gate.json" "$R/setup_root.json" "$R/build"
TLIB=$("$LEAN" --print-libdir)
AXG_LEAN=$LEAN AXG_LEAN_PATH=$TLIB:$PRF:$LIB:$R/build$MP AXG_SETUP=$R/setup_gate.json \
AXG_FROZEN_LEAN_PATH=$TLIB:${K30E_FROZEN:?}/build$MP AXG_FROZEN=$K30E_FROZEN AXG_STMT_COPY=${K30E_COPY:?} \
  bash "$T/axgate_k30e_v1.sh" "$R/gate" || rc=$?
echo "statement check rc=$rc"; cat "$R/gate/axgate_verdict.txt"
exit $rc
