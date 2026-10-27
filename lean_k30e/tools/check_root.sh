#!/bin/bash
# check_root.sh: the statement and axiom check of the shipped root, without rebuilding the data, the units, the parts or
# the root. It loads K30ER.Final from the supplement's public files and runs #print axioms and tools/axgate_k30e_v1.sh.
# Environment:
#   LEAN, MATHLIB_PKGS            as for build_proof.sh;
#   K30E_LIB, K30E_PROOF          the outputs of build_lib.sh and build_proof.sh;
#   K30E_DATAPUB                  K30E_DATA_PUBLICS.tar unpacked (the directory that holds K30EData/);
#   K30E_PARTS                    K30E_PARTS_ROOT.tar unpacked (the directory that holds build/K30EP and build/K30ER);
#   K30E_FROZEN                   ../lean (its SHA256SUMS lists Saw38a/Statements30e.lean), with K30E_FROZEN_BUILD = the
#                                 output of build_frozen.sh for it;
#   K30E_OUT                      a new work directory (setup files, check files, the statement check's outputs).
set -eu
T=$(cd "$(dirname "$0")" && pwd)
LEAN=${LEAN:-lean}; P=${MATHLIB_PKGS:?}; LIB=${K30E_LIB:?}; PRF=${K30E_PROOF:?}; DP=${K30E_DATAPUB:?}
PARTS=${K30E_PARTS:?}; FROZEN=${K30E_FROZEN:?}; FB=${K30E_FROZEN_BUILD:?}; O=${K30E_OUT:?}
SRC=$(cd "$T/.." && pwd)/src
MP=""
for d in mathlib batteries aesop Qq proofwidgets importGraph LeanSearchClient plausible Cli; do MP=$MP:$P/$d/.lake/build/lib/lean; done
mkdir -p "$O"
n=$(find "$PARTS/build/K30EP" -name 'P*.olean' | wc -l); [ "$n" -eq 3889 ] || { echo "part files: $n of 3889"; exit 3; }
[ -s "$PARTS/build/K30ER/Final.olean" ] || { echo "root K30ER/Final.olean missing"; exit 3; }
python3 "$T/gen_setup_v2.py" K30EP.BASE "$O/base_setup.json" "$LIB" "$DP"
python3 "$T/gen_setup_v4.py" ChkRoot "$O/setup_chk_root.json" "$O/base_setup.json" "$PARTS/build"
export LEAN_PATH=$PRF:$LIB$MP
printf 'module\npublic import K30ER.Final\n#print axioms Saw38a.K30EK.cert_exists\n#print axioms Saw38a.K30EK.bridge_bound\n#print axioms Saw38a.K30EK.connective_constant_le\n#print axioms Saw38a.K30EK.connective_constant_le_unconditional\n' > "$O/chk_root.lean"
"$LEAN" --setup "$O/setup_chk_root.json" -j1 "$O/chk_root.lean"
python3 "$T/gen_setup_v4.py" AxgateCheckK "$O/setup_gate.json" "$O/base_setup.json" "$PARTS/build"
TLIB=$("$LEAN" --print-libdir)
rc=0
AXG_LEAN=$LEAN AXG_LEAN_PATH=$TLIB:$PRF:$LIB:$PARTS/build$MP AXG_SETUP=$O/setup_gate.json \
AXG_FROZEN_LEAN_PATH=$TLIB:$FB$MP AXG_FROZEN=$FROZEN AXG_STMT_COPY=$SRC/Saw38a/Statements30e.lean \
  bash "$T/axgate_k30e_v1.sh" "$O/gate" || rc=$?
echo "statement check rc=$rc"; cat "$O/gate/axgate_verdict.txt"
exit $rc
