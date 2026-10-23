# Native controls on the full k30e certificate

Each file is a list of `native_decide` theorems over the full data (L38Data.All), so each module is meant to build.
A positive control states that the checker accepts (`= true`) or that a decoded child index equals the value in
k30e.chosen; a negative control states that the checker rejects (`= false`) or that a decoded index differs from a
corrupted value. A wrongly accepted negative input would stop the build.

- Ctl35.lean (written by ../../tools/gen_ctl35.py from k30e.chosen): bits 33 and 34 of the 35-bit child indices in
  each slot (6 positive, 6 negative); the 1000 states from index 2^34 pass, and fail with the bound N = 2^34 and with a
  misaligned record layout.
- CtlWorst.lean: state 7814884826 (the first C++ checker, checker/check_saw.cpp, attains the largest ratio there): the
  exact ratio passes for the state and for the 1000 states around it, and num - 1 fails.
- CtlWorst2.lean: the same at state 1944116169, where the independent C++ checker (independent/check38a.cpp) first
  attains the largest ratio (a tie).

Run: copy the files into ../../L38Shard/ after the build and `lake build L38Shard.Ctl35 L38Shard.CtlWorst
L38Shard.CtlWorst2`. The logs of our run are ctl35_gen.log, ctl35.log, ctlworst.log and ctlworst2.log ("Build
completed successfully" for each).
