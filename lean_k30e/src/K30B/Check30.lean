module

public import Saw38aK.CheckB2

@[expose] public section


/-!
# CheckB2 for the k30e certificate (baseline of the speedup study)                     

`checkStateB2` with the `∅` child index `NONE30 = 2^35 - 1` (k30e has 24,887,440,008 states, so 30-bit child indices
do not fit) and records of 224 bits: `n` (6), `T` (48), `c₀`, `c₁`, `c₂` (35 each), `V` (61). Everything else is the
frozen K26F checker (`childOKB2`, `confinedB`, `floodB`, `decodeO`, ...), unchanged.
-/

namespace K30B

open Saw38aCore Saw38aK

def NONE30 : Nat := 34359738367

def entryOK30 (rd : Nat → Rec) (N : Nat) (S : List (Nat × Nat)) (Sg : Nat) (b1 : Box) (t c : Nat) : Bool :=
  let tc := stepO t
  if c == NONE30 then
    memO Sg tc || confinedB Sg (floodB Sg b1 tc.1 tc.2) b1 tc.1 tc.2
  else
    decide (c < N) && (memO Sg tc ||
      (let r := rd c
       match decodeO r.n r.T with
       | none => false
       | some C => childOKB2 S Sg tc C))

def childV30 (rd : Nat → Rec) (c : Nat) : Nat := if c == NONE30 then 0 else (rd c).V

def checkState30 (rd : Nat → Rec) (N num den i : Nat) : Bool :=
  let r := rd i
  match decodeO r.n r.T with
  | none => false
  | some S =>
    let Sg := gridB S
    let b1 := bboxO S 1
    decide (0 < r.V) &&
      entryOK30 rd N S Sg b1 0 r.c0 && entryOK30 rd N S Sg b1 1 r.c1 &&
      entryOK30 rd N S Sg b1 2 r.c2 &&
      decide (den * (childV30 rd r.c0 + childV30 rd r.c1 + childV30 rd r.c2) ≤ num * r.V)

/-- All states of a list (sampled, not contiguous). -/
def checkList30 (rd : Nat → Rec) (N num den : Nat) : List Nat → Bool
  | [] => true
  | i :: is => checkState30 rd N num den i && checkList30 rd N num den is

/-- A record of 224 bits. -/
def recOf30 (x : Nat) : Rec :=
  ⟨x &&& 63, (x >>> 6) &&& 281474976710655, (x >>> 54) &&& 34359738367, (x >>> 89) &&& 34359738367,
    (x >>> 124) &&& 34359738367, (x >>> 159) &&& 2305843009213693951⟩

def recAt30 (leaf k : Nat) : Rec := recOf30 ((leaf >>> (224 * k)) &&& 26959946667150639794667015087019630673637144422540572481103610249215)

/-- Record `i` of a two-level table: leaves of `L` records, modules of `P` leaves (as `rdT`). -/
def rdT30 (top : BT (BT Nat)) (L P i : Nat) : Rec :=
  recAt30 (BT.get 0 (BT.get .leaf top (i / (L * P))) ((i / L) % P)) (i % L)

end K30B

end
