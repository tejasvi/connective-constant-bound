# A Lean proof that the connective constant of Z^2 is at most 2.6586513

Lean 4 (v4.35.0-rc3) with Mathlib at commit c55e6e786f49 (see lake-manifest.json).

## Main theorem
`Saw38a.K30E.connective_constant_le_unconditional` (Saw38a/Final.lean):

    ∃ μ : ℝ, Tendsto (fun n : ℕ => (sawCount n : ℝ) ^ ((1 : ℝ) / n)) atTop (𝓝 μ) ∧
      μ ≤ (105432502045487 : ℝ) / 39656386815908 ∧ μ < 2.6586513

`sawCount n` is the number of n-step self-avoiding walks on Z^2 that start at the origin, counted as step sequences
(Saw38a/Spec.lean). The theorem has no hypotheses. `#print axioms` gives the 3 standard axioms (propext,
Classical.choice and Quot.sound) and 181 `native_decide` axioms: one for `L38.Shard.start_ok` and 180 for the shards
`L38.Shard.shard000` to `L38.Shard.shard179`.

Statement files:
- `Saw38a/Statements30e.lean` holds the statements of this proof with `sorry` bodies. `probe/CheckFinal.lean` checks
  by `rfl` that the proved theorems have exactly these types.
- `Saw38a/Statements.lean` is the same file for a certificate of order 26; the proof does not use it.
- Final.lean imports neither statement file. Their `sorry` bodies make `lake build Saw38a` print "declaration uses
  `sorry`" warnings for these two files only.

## Contents
- Saw38a/Spec.lean: definitions.
  - Walks, `sawCount`, `bridgeCount`.
  - The Hammersley-Welsh bound `HW` in a weak form (a subexponential factor).
  - States, dead cells and certificates (Definitions 3.1 and 3.2 of the paper).
  - The number of paths of the automaton graph.
- Saw38aCore/Check.lean: the certificate checker, core Lean only, compiled to native code.
  - Records are 32 characters per state: the cell count and turn code (8 characters), three child indices of 35 bits
    (15 characters; 2^35 - 1 stands for "no child") and the weight (9 characters).
  - It checks (C1), (C2), positive weights and `den · Σ V(children) ≤ num · V` for every state.
  - Every claim that a cell cannot escape is re-checked by a closure test of the flood-fill result.
- Saw38a/CheckGrid.lean, CheckConf.lean, CheckDead.lean, CheckDecode.lean, CheckMain.lean: if the checker accepts
  every record, the records form a valid certificate (`valid_of_check`, `checkState_of_shards`).
- Saw38a/Bridge.lean: Theorem 4.1, b_n ≤ the number of automaton paths of length n.
- Saw38a/Count.lean: Lemma 5.1, the number of paths of length n is at most V_st · λ^n.
- Saw38a/Fekete.lean: c_{m+n} ≤ c_m c_n, and the limit μ exists.
- Saw38a/Mu.lean: `HW` and b_n ≤ C λ^n give μ ≤ λ.
- Saw38a/HW.lean: `hw' : HW`, with c_n ≤ (n+1)^(2⌊√(2n)⌋+1) b_(n+1).
- Saw38a/Final.lean: the assembly for the certificate of order 30 (file prefix k30e).
- L38Loader.lean: the build-time loader.
  - `load_cert_chunk name "path" hash` defines `name : String` from a data file after checking its 64-bit FNV-1a hash.
  - The definition is compiled and not inlined.
- tools/mkchunk30e.py and tools/gen_data30e.sh convert the certificate files into 11,497 chunk files of 32 seven-bit
  characters per state: 2,164,802 states each, the last has 876,216. They write the modules L38Data/ChunkNNNNN.lean
  and L38Data/All.lean. DATA_PINS.txt lists the length and FNV-1a hash of every chunk.
- lakefile.toml builds the compiled data as 5 libraries L38DataP0 to L38DataP4 (chunks 0-2299, 2300-4599, 4600-6899,
  6900-9199 and 9200-11496, about 159 GB each), whose root modules L38DataP0.lean to L38DataP4.lean import only their
  own chunks. L38Data.All belongs to the L38Shard library, which is not precompiled, so no shared library holds all
  chunks; the shards load the 5 libraries as plugins. Reason: Lake hashes each shared library by reading the whole
  file into memory, and a single 796 GB library ran out of memory on a machine with about 2 TB of RAM.
  tools/split_data_libs.py generated lakefile.toml and the 5 root modules from the single-library lakefile.
- tools/gen_shards30e.py writes L38Shard/Defs.lean, the 180 shard modules (138,547,328 states each; the last has
  87,468,296), L38Shard/Start.lean and L38Shard/All.lean.
- tools/gen_ctl35.py writes the native controls for the high bits of the child indices (controls/native/Ctl35.lean).

## Data
The certificate of order 30 (files k30e.keys, k30e.chosen, k30e.v) is in five records of the paper's supplement.
k30e.keys and byte ranges of k30e.chosen (four pieces) and k30e.v (five pieces) were compressed separately with xz:
- doi:10.5281/zenodo.23574056 holds k30e.keys.xz and k30e.chosen.part1.xz;
- doi:10.5281/zenodo.23574058 holds k30e.chosen.part2.xz and k30e.chosen.part3.xz;
- doi:10.5281/zenodo.23574060 holds k30e.chosen.part4.xz and k30e.v.part1.xz;
- doi:10.5281/zenodo.23574062 holds k30e.v.part2.xz and k30e.v.part5.xz;
- doi:10.5281/zenodo.23574064 holds k30e.v.part3.xz and k30e.v.part4.xz.
The sha256 values of the compressed files are:

    2666650fe83c65c2a4653973f256dc8ff640b51617c15b8781e6077def486d8d  k30e.keys.xz
    7b58ac22e168136d91017822c60972b38ee12d56ed003b9ca4871e2e632cf353  k30e.chosen.part1.xz
    6c2614f44979dcd94a8ce67549ceb36d87fdfab7f6b38f68f5d2d54665c7de3e  k30e.chosen.part2.xz
    0f4c722498bd8bd3eb27775aaa7edfcb78a200cf1b4d8c5b178f03f2b0ea7015  k30e.chosen.part3.xz
    769cbb866ccf71bb87bf21e05c01bd7657916fae64b799c928ef21638d579e48  k30e.chosen.part4.xz
    64b54eeffa168503b464d39c0174b78b5d91c2e1f45cee45ec0b1594c136dcc6  k30e.v.part1.xz
    b8fc195c1ea81d42af13323aaf2dee7c4f5b7b235da02633fecf688fcc8aec3a  k30e.v.part2.xz
    1a6416e72bb6ea21d31957a66adc74d1ecd0b447da15e157663f465036caebc3  k30e.v.part5.xz
    acff736d6e436931831b3da78f3d6e4061d1d5f45bf21080d85473c7903fda11  k30e.v.part3.xz
    e66a05539c19ab6584231d8085c0177323677d7c5017ef35f64d53b615efac24  k30e.v.part4.xz

Join the pieces of each file in order and decompress:

    xz -dc k30e.keys.xz > k30e.keys
    cat k30e.chosen.part1.xz k30e.chosen.part2.xz k30e.chosen.part3.xz k30e.chosen.part4.xz | xz -dc > k30e.chosen
    cat k30e.v.part1.xz k30e.v.part2.xz k30e.v.part3.xz k30e.v.part4.xz k30e.v.part5.xz | xz -dc > k30e.v

After decompression, the files have these sha256 values (checked by tools/gen_data30e.sh):
- keys 7a244666900ae95d404550871de6c076fcb57d75baa5dbf68d6af6c798bf64b8
- chosen c786235e644c5c547d5be02510561e3263baa55402c3042b676dffcdcc9700fa (64-bit indices)
- v fc4151469c10771fabc2605eb58db96390c15a2a42113c84d068dd5b2267e351
The certificate has 24,887,440,008 states, which become 796,398,080,256 characters of chunk data. The soundness of
the checker does not depend on the data; the data only determine which certificate is checked.

## Build
1. Download the ten xz files, then join and decompress them as in Data (995.5 GB after decompression).
2. Run `bash tools/gen_data30e.sh PREFIX`, where PREFIX is the absolute path of the files without the extension (default
   ~/l38/cert/k30e). The script checks the sha256 of the three files, converts them in parallel, and writes data/
   (796.4 GB of chunk data), pins/ and L38Data/. Compare pins/ with DATA_PINS.txt. The certificate files are not
   needed after this step.
3. `lake build L38DataP0:shared`, then the same for L38DataP1 to L38DataP4, one library at a time. In our run the
   chunk modules were compiled in one `lake build` of at most 75 minutes; each library link and hash then took
   226-242 s, with a peak resident memory of about 320 GB (mostly file pages of the linker).
4. `python3 tools/gen_shards30e.py .`, then `lake build L38Shard.SNNN` for NNN = 000 to 179.
   - Each shard is one `native_decide` that uses all cores.
   - The machine needs enough RAM to keep the 796 GB of libraries in the page cache.
   - On one machine with 128 threads and about 2 TB of RAM, the shards took 1,227,912 CPU-seconds and 3.3 hours in
     total: 45-218 s per shard, at most 116 GB of memory per shard.
5. `lake build Saw38a.Final` (about 70 s), then `lake env lean probe/CheckFinal.lean` (statements and axioms).
The build writes about 4.8 TB under .lake/, plus the 0.8 TB of chunk data, plus 1.0 TB for the decompressed
certificate unless it is deleted after step 2 (6.6 TB in all on our build machine). The proof modules without the
data, `lake build Saw38a`, build in a few minutes.

## Controls
- controls/ (see controls/README.md) reruns the small-certificate controls with this checker.
  - It accepts certificates of order 12, 14 and 16 built by the same program.
  - It rejects every corrupted variant: a child removed, children redirected, a weight halved, a claimed ratio below
    the true one, and builds of a variant of the program without the guard for loops with a gap cell (separate
    builds, not modifications).
  - For the certificates that violate (C1) or (C2), it reports the same number of failing states and the same first
    failing state as the independent C++ checker. In the ratio controls, its first failing state is the state where
    that checker attains the largest ratio.
- controls/native/ holds controls on the full certificate. Each is a list of `native_decide` theorems, so each module
  is meant to build. A positive control states that the checker accepts, or that a decoded child index equals the
  value in k30e.chosen. A negative control states that the checker rejects (`= false`), so a wrongly accepted input
  would stop the build.
  - Ctl35.lean (written by tools/gen_ctl35.py): for each child slot, a state whose child index has bit 33 set and one
    whose child index has bit 34 set decode to the 64-bit values in k30e.chosen, and not to those values without the
    bit. The 1000 states from index 2^34 pass, and fail with the bound N = 2^34 and with a misaligned record layout.
  - CtlWorst.lean: at state 7814884826, where the first C++ checker (checker/check_saw.cpp) attains the largest
    ratio, the exact ratio passes and num - 1 fails.
  - CtlWorst2.lean: the same at state 1944116169, where the independent C++ checker (independent/check38a.cpp) first
    attains the largest ratio (a tie).
  - To run them, copy the files into L38Shard/ and `lake build L38Shard.Ctl35 L38Shard.CtlWorst L38Shard.CtlWorst2`.
