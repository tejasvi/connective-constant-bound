#!/bin/bash
# build_proof.sh [OUT [LIB]]: build the 22 modules of the proof layer (src/Saw38a, src/Saw38aKP, src/K30BP) in dependency
# order into OUT (default: build_proof), against the library built by build_lib.sh in LIB (default: build_lib).
# Run from lean_k30e/. Environment: LEAN (default: lean on PATH; v4.35.0-rc3); MATHLIB_PKGS = the .lake/packages
# directory of a Lake project with Mathlib at c55e6e786f49 (see lake-manifest.json), already built.
set -eu
LEAN=${LEAN:-lean}; P=${MATHLIB_PKGS:?set MATHLIB_PKGS}
OUT=$(mkdir -p "${1:-build_proof}" && cd "${1:-build_proof}" && pwd); LIB=$(cd "${2:-build_lib}" && pwd)
LP=$OUT:$LIB
for d in mathlib batteries aesop Qq proofwidgets importGraph LeanSearchClient plausible Cli; do LP=$LP:$P/$d/.lake/build/lib/lean; done
export LEAN_PATH=$LP
for m in Saw38a.Spec Saw38a.Bridge Saw38a.Count Saw38a.Fekete Saw38a.HW Saw38a.Mu Saw38a.Statements30e Saw38a.CheckGrid \
    Saw38a.CheckDecode Saw38a.CheckConf Saw38a.CheckDead Saw38a.CheckMain Saw38aKP.Grid Saw38aKP.Close Saw38aKP.DecodeO \
    Saw38aKP.DeadB Saw38aKP.MainB K30BP.Walk K30BP.Child K30BP.Main3c K30BP.Look K30BP.Unit; do
  f=src/$(echo $m | tr . /).lean; o=$OUT/$(echo $m | tr . /).olean; mkdir -p "$(dirname "$o")"
  "$LEAN" -DElab.async=false -j1 -R src -o "$o" "$f"
  echo "built $m"
done
