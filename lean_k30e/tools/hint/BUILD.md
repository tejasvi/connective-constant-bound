# k30hint (K30E hint tool)

k30hint is an untrusted tool. For the states of one unit it writes the hint rows `i|h|[d0]|[d1]|[d2]` that the unit
sources embed. It also evaluates the compiled `checkState3cL` first, so a failing state stops its unit before any
kernel time is spent. The kernel checks every hint again inside the unit, so a wrong hint can only make a unit fail.

Usage: `k30hint DATADIR NT NUM DEN LO CNT MODS OUT` (see the header of K30Hint.lean); ../unit/k30unit_v1.sh calls it.

## Build

From this directory, with lean-toolchain (leanprover/lean4:v4.35.0-rc3) and the library sources in ../../src:

    mkdir -p src && cp K30Hint.lean src/
    cp -r ../../src/Saw38aCore ../../src/K30B src/
    mkdir -p src/Saw38aK && cp ../../src/Saw38aK/Check*.lean src/Saw38aK/
    lake build k30hint

The result is `.lake/build/bin/k30hint`. The Lean runtime is linked into the binary, which needs only glibc (libc,
libm, libpthread, libdl, librt).

## Checking a rebuild

The binary used for the proof had sha256 7e224b00f5b133d4c9b795e656a74020ca42b28d5188f9a0e14ffa1afef8ae49. A rebuild
is checked by its output rows, not by its bytes: for the 25,000 states from index 24,887,350,000 (unit
K30ES.D0995.S995494, n = 31) the rows have sha256 681015460f9ae88298498d4ea7b26b00efc5241d811196d654f9e64159b0b2f3.
