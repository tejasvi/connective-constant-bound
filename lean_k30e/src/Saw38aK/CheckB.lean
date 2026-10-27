module

public import Saw38aK.CheckK

@[expose] public section


/-!
# Bitboard form of the kernel checker

`checkStateB` computes the same Boolean as `checkStateK` (theorem `checkStateB_eq` in `Saw38aKP/BridgeB.lean`)
with natural-number arithmetic on the hot paths:

* cells in offset coordinates `(x + 31, y + 31)`;
* a grid is one natural number, the cell `(x, y)` at bit `64 y + x` (`memB`, `setB`, `gridB`; `toGrid` is the
  63-row grid of a bitboard);
* `decodeO` decodes a state in offset coordinates (offset 64 while walking, so no subtraction truncates);
* the first pass of the child test (a symmetry mapping the child into `E`) uses bit tests only.

The rare paths call the kernel checker's functions on `toGrid` of the bitboards: dead-cell tests (`deadTestK`) and
trapped steps (`confinedK`, `floodK`).
-/

namespace Saw38aK

open Saw38aCore

/-! ## Bitboards -/

/-- Membership of the offset cell `(x, y)` (false outside `[0, 62]²`). -/
def memB (v x y : Nat) : Bool := decide (x < 63) && decide (y < 63) && v.testBit (64 * y + x)

def setB (v x y : Nat) : Nat := v ||| 2 ^ (64 * y + x)

/-- The 63-row grid of a bitboard (row `y` = bits `64 y .. 64 y + 62`). -/
def toGrid (v : Nat) : Grid := gridOfBB v

def memO (v : Nat) (c : Nat × Nat) : Bool := memB v c.1 c.2

def gridB (S : List (Nat × Nat)) : Nat := S.foldl (fun v c => setB v c.1 c.2) 0

/-- The offset coordinates of a cell. -/
def offC (c : Cell) : Nat × Nat := (ox c.1, ox c.2)

/-- The cell of offset coordinates `(x, y)` (as `Saw38a.cellOf`). -/
def cellOfK (x y : Nat) : Cell := ((x : Int) - 31, (y : Int) - 31)

/-! ## Decoding in offset coordinates -/

/-- One cell back from `c` against the step with direction index `i` (`0 = (1,0)`, `1 = (0,1)`, `2 = (-1,0)`,
`3 = (0,-1)`). -/
def stepBack (i : Nat) (c : Nat × Nat) : Nat × Nat :=
  if i == 0 then (c.1 - 1, c.2) else if i == 1 then (c.1, c.2 - 1) else if i == 2 then (c.1 + 1, c.2)
  else (c.1, c.2 + 1)

/-- The direction index after the turn digit `t` (as `turnBack`). -/
def turnIdx (t i : Nat) : Nat := if t = 1 then (i + 3) % 4 else if t = 2 then (i + 1) % 4 else i

/-- `back` in offset coordinates, with the step as a direction index. -/
def backO : Nat → Nat × Nat → List Nat → List (Nat × Nat) → List (Nat × Nat)
  | _, _, [], acc => acc
  | i, c, t :: ts, acc =>
    let i' := turnIdx t i
    let c' := stepBack i' c
    backO i' c' ts (c' :: acc)

/-- `small` at offset 64. -/
def small64 (c : Nat × Nat) : Bool := 36 ≤ c.1 && c.1 ≤ 92 && 36 ≤ c.2 && c.2 ≤ 92

/-- `nodupC` on offset cells. -/
def nodupO : List (Nat × Nat) → Bool
  | [] => true
  | c :: cs => cs.all (fun d => d.1 != c.1 || d.2 != c.2) && nodupO cs

def shift33 (c : Nat × Nat) : Nat × Nat := (c.1 - 33, c.2 - 33)

/-- `decode` in offset coordinates: the path is walked at offset 64, checked, and returned at offset 31. -/
def decodeO (n T : Nat) : Option (List (Nat × Nat)) :=
  if n < 2 || 40 < n then none
  else if (digitsQ (n - 2) T).2 != 0 then none
  else
    let q := backO 0 (63, 64) (digitsQ (n - 2) T).1 [(63, 64), (64, 64)]
    if q.all small64 && nodupO q then some (q.map shift33) else none

/-! ## Children, entries, states -/

/-- `d4c g` in offset coordinates. -/
def d4o (g : Nat) (z : Nat × Nat) : Nat × Nat :=
  if g == 0 then z else if g == 1 then (62 - z.2, z.1) else if g == 2 then (62 - z.1, 62 - z.2)
  else if g == 3 then (z.2, 62 - z.1) else if g == 4 then (z.1, 62 - z.2) else if g == 5 then (62 - z.1, z.2)
  else if g == 6 then (z.2, z.1) else (62 - z.2, 62 - z.1)

/-- `addC w t` in offset coordinates, for a step `t` (offsets `(32,31)`, `(31,32)`, `(31,30)`). -/
def addO (w t : Nat × Nat) : Nat × Nat := (w.1 + t.1 - 31, w.2 + t.2 - 31)

/-- `stepC t` in offset coordinates. -/
def stepO (t : Nat) : Nat × Nat := if t == 0 then (32, 31) else if t == 1 then (31, 32) else (31, 30)

/-- `bboxE` of offset cells. -/
def bboxO (cs : List (Nat × Nat)) (e : Nat) : Box :=
  let xs := cs.map fun c => c.1
  let ys := cs.map fun c => c.2
  ⟨xs.foldl min 62 - e, xs.foldl max 0 + e, ys.foldl min 62 - e, ys.foldl max 0 + e⟩

/-- A dead-cell test: `deadTestK` on the grids of the bitboards. -/
def deadTestB (Sg Eg : Nat) (eb bigb : Box) (t w : Nat × Nat) : Bool :=
  deadTestK (toGrid Sg) (toGrid Eg) eb bigb (cellOfK t.1 t.2) (cellOfK w.1 w.2)

/-- (C2) for the child with offset cells `C`, as `childOKK`. -/
def childOKB (S : List (Nat × Nat)) (Sg : Nat) (t : Nat × Nat) (C : List (Nat × Nat)) : Bool :=
  let Eg := setB Sg t.1 t.2
  (List.range 8).any (fun g => C.all fun z => memO Eg (addO (d4o g z) t)) ||
    (let eb := bboxO (t :: S) 0
     let bigb : Box := ⟨eb.x0 - 3, eb.x1 + 3, eb.y0 - 3, eb.y1 + 3⟩
     (List.range 8).any fun g => C.all fun z =>
       let w := addO (d4o g z) t
       memO Eg w || deadTestB Sg Eg eb bigb t w)

/-- The entry of slot `t` (child index `c`), as `entryOKK`. -/
def entryOKB (rd : Nat → Rec) (N : Nat) (S : List (Nat × Nat)) (Sg : Nat) (b1 : Box) (t c : Nat) : Bool :=
  let tc := stepO t
  if c == NONEK then
    memO Sg tc || confinedK (toGrid Sg) (floodK (toGrid Sg) b1 tc.1 tc.2) b1 tc.1 tc.2
  else
    decide (c < N) && (memO Sg tc ||
      (let r := rd c
       match decodeO r.n r.T with
       | none => false
       | some C => childOKB S Sg tc C))

/-- The check of state `i`, as `checkStateK`. -/
def checkStateB (rd : Nat → Rec) (N num den i : Nat) : Bool :=
  let r := rd i
  match decodeO r.n r.T with
  | none => false
  | some S =>
    let Sg := gridB S
    let b1 := bboxO S 1
    decide (0 < r.V) &&
      entryOKB rd N S Sg b1 0 r.c0 && entryOKB rd N S Sg b1 1 r.c1 &&
      entryOKB rd N S Sg b1 2 r.c2 &&
      decide (den * (childVK rd r.c0 + childVK rd r.c1 + childVK rd r.c2) ≤ num * r.V)

/-- The states `lo, …, lo + k - 1`. -/
def checkRangeB (rd : Nat → Rec) (N num den lo k : Nat) : Bool :=
  allFrom (checkStateB rd N num den) lo k

end Saw38aK

end
