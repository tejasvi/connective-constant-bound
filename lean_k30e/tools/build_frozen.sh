#!/bin/bash
# build_frozen.sh SRC OUT: plain build of SRC/Saw38a/Spec.lean and SRC/Saw38a/Statements30e.lean (SRC = ../lean, the
# native_decide proof whose statement file is matched) into OUT, for the statement check's frozen side.
# Environment: LEAN (default: lean on PATH); MATHLIB_PKGS as for build_proof.sh.
set -eu
LEAN=${LEAN:-lean}; P=${MATHLIB_PKGS:?set MATHLIB_PKGS}
SRC=$(cd "${1:?SRC}" && pwd); OUT=$(mkdir -p "${2:?OUT}" && cd "${2:?OUT}" && pwd)
LP=$OUT
for d in mathlib batteries aesop Qq proofwidgets importGraph LeanSearchClient plausible Cli; do LP=$LP:$P/$d/.lake/build/lib/lean; done
export LEAN_PATH=$LP
for m in Saw38a.Spec Saw38a.Statements30e; do
  f=$SRC/$(echo $m | tr . /).lean; o=$OUT/$(echo $m | tr . /).olean; mkdir -p "$(dirname "$o")"
  "$LEAN" -DElab.async=false -j1 -R "$SRC" -o "$o" "$f"
  echo "built $m"
done
