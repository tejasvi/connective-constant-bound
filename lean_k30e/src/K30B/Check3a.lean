module

public import K30B.Check30

@[expose] public section


/-!
# Variant 3a: children are walked, not re-validated (speedup study)

A child record `c < N` is itself checked in its own `checkState`, which validates its decode (range of `n`, no excess
digits, `small`, no repeated cell). So a parent's slot test can use the cells of the unvalidated walk `walkO`: when
`decodeO n T = some C`, `walkO n T = C` (to be proved: `walkO_of_decodeO`), and `valid_of_check` already has every
state's own check (`hall`).
-/

namespace K30B

open Saw38aCore Saw38aK

/-- The cells of the path with cell count `n` and turn code `T` (as `decodeO`, without its checks). -/
def walkO (n T : Nat) : List (Nat × Nat) :=
  (backO 0 (63, 64) (digitsQ (n - 2) T).1 [(63, 64), (64, 64)]).map shift33

def entryOK3a (rd : Nat → Rec) (N : Nat) (S : List (Nat × Nat)) (Sg : Nat) (b1 : Box) (t c : Nat) : Bool :=
  let tc := stepO t
  if c == NONE30 then
    memO Sg tc || confinedB Sg (floodB Sg b1 tc.1 tc.2) b1 tc.1 tc.2
  else
    decide (c < N) && (memO Sg tc || (let r := rd c; childOKB2 S Sg tc (walkO r.n r.T)))

def checkState3a (rd : Nat → Rec) (N num den i : Nat) : Bool :=
  let r := rd i
  match decodeO r.n r.T with
  | none => false
  | some S =>
    let Sg := gridB S
    let b1 := bboxO S 1
    decide (0 < r.V) &&
      entryOK3a rd N S Sg b1 0 r.c0 && entryOK3a rd N S Sg b1 1 r.c1 &&
      entryOK3a rd N S Sg b1 2 r.c2 &&
      decide (den * (childV30 rd r.c0 + childV30 rd r.c1 + childV30 rd r.c2) ≤ num * r.V)

def checkList3a (rd : Nat → Rec) (N num den : Nat) : List Nat → Bool
  | [] => true
  | i :: is => checkState3a rd N num den i && checkList3a rd N num den is

/-! ## Decode components (timing only) -/

def sumCells (cs : List (Nat × Nat)) : Nat := cs.foldl (fun a c => a + c.1 + c.2) 0

/-- Walk only (digits and cells), forced. -/
def pW (rd : Nat → Rec) (i : Nat) : Bool := decide (0 < sumCells (walkO (rd i).n (rd i).T)) || true

/-- Walk and `small64`, forced. -/
def pWS (rd : Nat → Rec) (i : Nat) : Bool :=
  (let q := backO 0 (63, 64) (digitsQ ((rd i).n - 2) (rd i).T).1 [(63, 64), (64, 64)]; q.all small64) || true

/-- The full decode, forced. -/
def pDec (rd : Nat → Rec) (i : Nat) : Bool := (decodeO (rd i).n (rd i).T).isSome || true

def listW (rd : Nat → Rec) (_N _num _den : Nat) : List Nat → Bool
  | [] => true
  | i :: is => pW rd i && listW rd _N _num _den is

def listWS (rd : Nat → Rec) (_N _num _den : Nat) : List Nat → Bool
  | [] => true
  | i :: is => pWS rd i && listWS rd _N _num _den is

def listDec (rd : Nat → Rec) (_N _num _den : Nat) : List Nat → Bool
  | [] => true
  | i :: is => pDec rd i && listDec rd _N _num _den is

end K30B

end
