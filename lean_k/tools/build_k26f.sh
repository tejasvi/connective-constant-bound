#!/bin/bash
# build_k26f.sh STEP [JOBS]: build the kernel-only K26F proof with plain `lean`, from the lean_k directory, after
# `lake exe cache get` (Mathlib). Sources are in src/ and every module is compiled with the working directory src/
# (the data modules read ../data/m%04d.bin). Outputs go to build/, logs to logs/. JOBS parallel processes (default nproc).
#   lib    : Saw38aCore, Saw38a, Saw38aK, Saw38aKP (the checker, its soundness, the audited k30e definitions)
#   data   : checks data/m0000.bin..m0915.bin (from the data archives) against data/MANIFEST.tsv, builds
#            K26FData/M0000..M0915 and K26FData/Top, then K26F/FinalAt and K26F/StatementCheckAt
#   shards : generates (tools/gen_k26f.py) and builds K26FS/Dddd/Skkkkk for k = 0..48023: the bulk of the work,
#            about one CPU-hour per shard
#   final  : generates and builds the parts K26FP/P000..P187, then K26F/Root, K26F/Final, K26F/StatementCheck (prints
#            the axioms) and K26F/Controls
# Compiling a module checks every theorem in it with the kernel. Shard/part/root sources can be compared with
# data/GENERATED_SHA256SUMS (cd src && sha256sum -c ../data/GENERATED_SHA256SUMS).
set -u
STEP=$1; J=${2:-$(nproc)}
cd "$(dirname "$0")/.." || exit 2
K=$PWD
LP=$(lake env printenv LEAN_PATH) || { echo "lake env failed (run lake exe cache get first)"; exit 2; }
export K LEAN_PATH="$K/build:$LP"
mkdir -p build logs
cd src || exit 2
one() {  # one MODULE_FILE relative to src/, e.g. Saw38aK/CheckB2.lean
  m=$1; b=${m%.lean}; mkdir -p "$K/build/$(dirname "$b")"
  lean -j 1 -o "$K/build/$b.olean" -i "$K/build/$b.ilean" "$m" > "$K/logs/$(echo "$b" | tr '/' '_').log" 2>&1
  rc=$?; echo "$m rc=$rc" >> "$K/logs/build.log"; return $rc
}
export -f one
inorder() { for m in "$@"; do one "$m" || { echo "FAILED $m (see logs/)"; exit 1; }; done; }
case $STEP in
  lib)
    inorder Saw38aCore/Check.lean Saw38a/Spec.lean Saw38a/CheckGrid.lean Saw38a/CheckConf.lean Saw38a/CheckDead.lean \
      Saw38a/CheckDecode.lean Saw38a/CheckMain.lean Saw38a/Bridge.lean Saw38a/Count.lean Saw38a/Fekete.lean \
      Saw38a/Mu.lean Saw38a/HW.lean Saw38a/Statements.lean Saw38aK/CheckK.lean Saw38aK/Lit.lean Saw38aK/LitBin.lean \
      Saw38aK/CheckB.lean Saw38aK/CheckB2.lean Saw38aK/RangeB.lean Saw38aKP/Grid.lean Saw38aKP/Close.lean \
      Saw38aKP/DeadB.lean Saw38aKP/DecodeO.lean Saw38aKP/MainB.lean ;;
  data)
    awk -F'\t' '{printf "%s  m%04d.bin\n", $6, $1}' ../data/MANIFEST.tsv | (cd ../data && sha256sum -c --quiet) \
      || { echo "data/m*.bin do not match data/MANIFEST.tsv"; exit 1; }
    ls K26FData/M*.lean | xargs -P "$J" -n 1 bash -c 'one "$0"' || exit 1
    inorder K26FData/Top.lean K26F/FinalAt.lean K26F/StatementCheckAt.lean ;;
  shards)
    seq 0 48023 | xargs -P "$J" -n 1 bash -c \
      'f=$(printf "K26FS/D%03d/S%05d.lean" $(($0 / 1000)) $0); [ -f "$K/build/${f%.lean}.olean" ] && exit 0
       python3 ../tools/gen_k26f.py . shard $0 20000 100 && one "$f"' || exit 1 ;;
  final)
    python3 ../tools/gen_k26f.py . parts 20000 256 || exit 1
    ls K26FP/P*.lean | xargs -P "$J" -n 1 bash -c 'one "$0"' || exit 1
    inorder K26F/Root.lean K26F/Final.lean K26F/StatementCheck.lean K26F/Controls.lean
    cat "$K/logs/K26F_StatementCheck.log" ;;
  *) echo "usage: bash tools/build_k26f.sh lib|data|shards|final [JOBS]"; exit 2 ;;
esac
echo "$STEP done"
