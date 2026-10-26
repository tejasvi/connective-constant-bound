# Controls of the native checker

Positive and negative controls of `Saw38aCore.checkRange` on small certificates built by the paper's construction
program. The checker is in ../Saw38aCore/Check.lean and reads records of 32 characters with child indices of 35 bits.
ctl_table.txt lists the controls. logs/ holds the reference runs of the independent C++ checker (chk_*.out, with exit
codes and times in chk_summary.txt) and the Lean build logs (lake_*.log).

The certificates are not included and must be regenerated:
- ok_k12, ok_k14, ok_k16: the construction program at orders 12, 14 and 16 with rules PBXbSTU72q and default tables.
- gap_k12, gap_k14, gap_k16: separate builds by the variant of the program without the guard for loops with a gap cell
  (independent/gaploop_guard_removed.patch of the supplement).
- mut_kK/mut_M1_dropchild, mut_M2_redirect, mut_M3_lowv: independent/mutate_cert.py from the supplement applied to
  ok_kK, with the states 1249, 5512 and 17751 for K = 12, 14 and 16, the state printed on each certificate's LAM line.
  - M1 empties the +x slot of state 0.
  - M2 redirects children.
  - M3 halves one weight.
- `bash make_certs.sh SAW_CPP INDEPENDENT_DIR` builds them under certs/, compares their sha256 with
  independent/generated_SHA256SUMS and writes the C++ checker's outputs to logs/chk_NAME.out. SAW_CPP is
  builder/previous/saw.cpp of the supplement, the version that independent/gaploop_guard_removed.patch applies to; it
  builds the same small certificates as builder/saw.cpp. INDEPENDENT_DIR is the supplement's independent/ directory.
  With GCC 15.2 on x86-64, all 27 files match (logs/cert_sha_check.txt).
- The `chosen` files of these certificates hold 32-bit indices; tools/mkchunk30e.py writes their "no child" value as
  2^35 - 1, the value that the checker expects.

Run:
1. Copy ../Saw38aCore, ../Saw38aCore.lean, ../L38Loader.lean and ../tools here, and lean-toolchain from ../.
2. `bash make_certs.sh SAW_CPP INDEPENDENT_DIR` (see above).
3. `python3 gen_ctl.py`: writes data/, CtlData/, CtlCheck/ and CtlReport/. It uses tools/mkchunk30e.py.
4. `lake build CtlCheck`: 18 `native_decide` theorems. The 3 good certificates give `checkRange ... = true`; all
   others give `= false`.
5. `lake build CtlReport`: for each control, `#eval` prints the verdict, the number of failing states and the first
   failing state.
6. Optional: `python3 gen_ctl_par.py` and `lake build CtlCheckPar` run the order-16 controls split into 7 chunks of
   10000 states (the last one partial), with checkRange and checkRangePar.

Expected: for the certificates that violate (C1) or (C2), the number of failing states and the first failing state
equal those of the C++ checker (logs/chk_*.out). In the ratio controls (a weight halved, or a claimed ratio with the
numerator lowered by one), the C++ checker reports a global ratio mismatch with 0 failing states. Lean flags the state
or states where that checker attains the largest ratio.
