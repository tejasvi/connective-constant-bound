import Lean
import Saw38aK.Lit

/-!
# Build-time loader of packed record leaves (untrusted)

`bt_bin% "path" n w` reads the binary file `path` (relative to the working directory of the build): `n` leaves of
`w` bytes each, little endian. It elaborates to the Braun tree (`BT Nat`) of the leaves as raw natural-number literals.
The kernel checks every statement about the resulting terms; the loader only decides which data are checked, so its
correctness does not matter for soundness. The files are pinned by their sha256 in the data manifest.
-/

namespace Saw38aK

open Lean Elab Term Meta

/-- The natural number of the little-endian bytes `a[off], …, a[off + len - 1]` (divide and conquer). -/
partial def natOfBytes (a : ByteArray) (off len : Nat) : Nat :=
  if len ≤ 64 then
    (List.range len).foldr (fun i acc => acc * 256 + (a.get! (off + i)).toNat) 0
  else
    let h := len / 2
    natOfBytes a off h + (natOfBytes a (off + h) (len - h) <<< (8 * h))

elab "bt_bin% " p:str n:num w:num : term => do
  let a ← IO.FS.readBinFile p.getString
  let n := n.getNat
  let w := w.getNat
  if a.size != n * w then throwError "bt_bin%: {p.getString} has {a.size} bytes, expected {n * w}"
  let xs := (Array.range n).map fun i => mkRawNatLit (natOfBytes a (i * w) w)
  return braunExpr (mkConst ``Nat) xs

end Saw38aK
