module

public import Saw38aCore.Check

@[expose] public section


/-!
# Kernel-evaluable checker for 38a memory-automaton certificates

The checks of `Saw38aCore.checkState`, in a form the Lean kernel can evaluate (`decide +kernel`, no compiled code).
Every checked claim uses the same functions as the native checker (`decode`, `gridOf`, `mem`, `memN`, `nbCount`,
`closedIn`, `tNbrsOK`, `bboxE`, `allFrom`), so the soundness proofs carry over. Three things change:

1. The untrusted helpers `flood`, `touchesRing` and `pathToRing` use `while` loops, which compile to `partial`
   functions that the kernel cannot unfold. `floodK`, `touchesRingK` and `pathToRingK` replace them: structural
   recursion on a fuel argument, on bitboards (the cell `(x, y)` is bit `64 y + x` of one natural number). Their
   results are only used through checked claims (`confinedK` ends in `closedIn`; every candidate of `candsK` passes
   `testCK`), so they need no proof.
2. Records come from a function `rd : Nat → Rec` (the data layer), not from `readRec chunks cs`.
3. The child index `NONEK = 2^30 - 1` stands for the symbol `∅`.
-/

namespace Saw38aK

open Saw38aCore

/-! ## Bitboards (untrusted) -/

/-- The bits `x0..min x1 62` of a row. -/
def maskK (x0 x1 : Nat) : Nat := (2 ^ (min x1 62 + 1) - 1) ^^^ (2 ^ x0 - 1)

/-- The free cells (in the row mask `m`, not blocked) of the rows `r, r + 1, …` (`k` rows), as a bitboard. -/
def freeBB (blocked : Grid) (m : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | k + 1, r, acc => freeBB blocked m k (r + 1) (acc ||| ((m ^^^ (blocked[r]! &&& m)) <<< (64 * r)))

/-- One step of 4-neighbour growth (bits that leave a row land on bit 63 of a row, which is never free). -/
def growBB (v : Nat) : Nat := v ||| (v <<< 1) ||| (v >>> 1) ||| (v <<< 64) ||| (v >>> 64)

/-- Grow `v` inside `free` until it stops changing (at most `fuel` steps). -/
def floodBB (free : Nat) : Nat → Nat → Nat
  | 0, v => v
  | f + 1, v =>
    let nv := growBB v &&& free
    if nv == v then v else floodBB free f nv

/-- The rows `0..k-1` of a bitboard. -/
def rowsOfBB (v : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => (v &&& 9223372036854775807) :: rowsOfBB (v >>> 64) k

/-- The grid (63 rows) of a bitboard. -/
def gridOfBB (v : Nat) : Grid := ⟨rowsOfBB v 63⟩

/-- The bitboard of a grid (rows `r, r + 1, …`, `k` rows). -/
def bbOfGrid (g : Grid) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | k + 1, r, acc => bbOfGrid g k (r + 1) (acc ||| (g[r]! <<< (64 * r)))

/-- 4-connected flood fill from `(sx, sy)` over the cells of the box that are not blocked (replaces `flood`). -/
def floodK (blocked : Grid) (bx : Box) (sx sy : Nat) : Grid :=
  let free := freeBB blocked (maskK bx.x0 bx.x1) (min bx.y1 62 + 1 - bx.y0) bx.y0 0
  let s := 64 * sy + sx
  if sx > 62 || (free >>> s) &&& 1 == 0 then emptyG
  else gridOfBB (floodBB free 4096 (2 ^ s))

/-- The rows `r, …, r + k - 1` of `f` meet `edges`. -/
def edgesHit (f : Grid) (edges : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | k + 1, r => (f[r]! &&& edges != 0) || edgesHit f edges k (r + 1)

/-- The filled region meets the outermost ring of the box (replaces `touchesRing`; a filter before `closedIn`). -/
def touchesRingK (f : Grid) (bx : Box) : Bool :=
  let m := maskK bx.x0 bx.x1
  (f[bx.y0]! &&& m != 0) || (f[bx.y1]! &&& m != 0) ||
    edgesHit f (2 ^ bx.x0 ||| 2 ^ bx.x1) (bx.y1 - 1 - bx.y0) (bx.y0 + 1)

/-- `R` (inside the box) contains `(x, y)` and is closed (as `confined`, with `touchesRingK`). -/
@[inline] def confinedK (blk R : Grid) (b : Box) (x y : Nat) : Bool :=
  b.x1 ≤ 62 && b.y1 ≤ 62 && b.x0 ≤ x && x ≤ b.x1 && b.y0 ≤ y && y ≤ b.y1 && memN R x y && !touchesRingK R b &&
    closedIn blk R b

/-! ## One shortest path to the ring (untrusted; replaces `pathToRing`) -/

/-- The cells of the box ring and outside it, as a bitboard (rows `0..62`, columns `0..62`). -/
def ringRowK (bx : Box) (r : Nat) : Nat :=
  if r ≤ bx.y0 || r ≥ bx.y1 then 9223372036854775807
  else (2 ^ (min bx.x0 62 + 1) - 1) ||| (9223372036854775807 ^^^ (2 ^ (min bx.x1 63) - 1))

def ringBB (bx : Box) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | k + 1, r, acc => ringBB bx k (r + 1) (acc ||| (ringRowK bx r <<< (64 * r)))

/-- Breadth-first layers from the layer list `ls` (newest first) inside `fl`, until a layer meets `ring`; returns
the layers (newest first) with `true` if the ring was reached. -/
def layersBB (fl ring : Nat) : Nat → Nat → List Nat → List Nat × Bool
  | 0, _, ls => (ls, false)
  | f + 1, vis, ls =>
    match ls with
    | [] => ([], false)
    | cur :: _ =>
      let nx := (growBB cur &&& fl) ^^^ ((growBB cur &&& fl) &&& vis)
      if nx == 0 then (ls, false)
      else if nx &&& ring != 0 then (nx :: ls, true)
      else layersBB fl ring f (vis ||| nx) (nx :: ls)

/-- The index of the lowest set bit of `v` (scanning `k` positions from `i`; `i + k` if none). -/
def lowBit (v : Nat) : Nat → Nat → Nat
  | 0, i => i
  | k + 1, i => if (v >>> i) &&& 1 == 1 then i else lowBit v k (i + 1)

/-- A neighbour of bit `c` in the bitboard `L` (the first of `c + 1, c - 1, c + 64, c - 64`). -/
def nbrIn (L c : Nat) : Nat :=
  if (L >>> (c + 1)) &&& 1 == 1 then c + 1
  else if c ≥ 1 && (L >>> (c - 1)) &&& 1 == 1 then c - 1
  else if (L >>> (c + 64)) &&& 1 == 1 then c + 64
  else c - 64

/-- Walk back through the older layers (`ls`, newest first, the start layer last), from bit `c`. -/
def backBB : List Nat → Nat → List (Nat × Nat) → List (Nat × Nat)
  | [], _, acc => acc
  | [_], _, acc => acc
  | L :: rest, c, acc =>
    let c' := nbrIn L c
    backBB rest c' ((c' % 64, c' / 64) :: acc)

/-- Cells after the first on one shortest 4-connected path from `(x, y)` through cells of `fl` to the ring of the box
(the start excluded, the ring cell included). -/
def pathToRingK (fl : Grid) (bx : Box) (x y : Nat) : Array (Nat × Nat) :=
  let flb := bbOfGrid fl 63 0 0
  let ring := ringBB bx 63 0 0
  let s := 2 ^ (64 * y + x)
  if s &&& ring != 0 then #[]
  else
    match layersBB flb ring 4096 s [s] with
    | (top :: rest, true) =>
      let g := lowBit (top &&& ring) 4096 0
      (backBB rest g [(g % 64, g / 64)]).toArray
    | _ => #[]

/-! ## Dead cells (as in `Saw38aCore`, with the replaced helpers) -/

/-- Candidates for the cell `w` of test (c) (untrusted), as `cands`. -/
def candsK (Eg : Grid) (eb : Box) (fl : Grid) (bigb : Box) (x y : Nat) : Array (Nat × Nat) :=
  let _ := eb
  (pathToRingK fl bigb x y).filter fun c =>
    let xx := c.1
    let yy := c.2
    xx ≥ 1 && yy ≥ 1 && !memN Eg xx yy && ((Eg[yy - 1]! ||| Eg[yy]! ||| Eg[yy + 1]!) >>> (xx - 1)) &&& 7 != 0

/-- Test (c) for the cell `(wx, wy)`, as `testC`. -/
@[inline] def testCK (Eg : Grid) (bigb : Box) (t : Cell) (x y wx wy : Nat) : Bool :=
  let Bw := setN Eg wx wy
  let f2 := floodK Bw bigb x y
  wx ≤ 62 && wy ≤ 62 && !memN Eg wx wy && !(wx == x && wy == y) && confinedK Bw f2 bigb x y && tNbrsOK Bw f2 t

/-- The cell `w` (outside `E`) is dead for `(S, t)`, as `deadTest`. -/
def deadTestK (Sg Eg : Grid) (eb bigb : Box) (t w : Cell) : Bool :=
  inRange w &&
    (decide (3 ≤ nbCount Sg w) ||
      (let x := ox w.1
       let y := ox w.2
       let fl := floodK Eg bigb x y
       confinedK Eg fl bigb x y ||
         (bigb.x0 < x && x < bigb.x1 && bigb.y0 < y && y < bigb.y1 &&
           (candsK Eg eb fl bigb x y).any fun c => testCK Eg bigb t x y c.1 c.2)))

/-- (C2) for the child with cells `C`, as `childOK`. -/
def childOKK (S : List Cell) (Sg : Grid) (t : Cell) (C : List Cell) : Bool :=
  let Eg := add Sg t
  (List.range 8).any (fun g => C.all fun z => mem Eg (addC (d4c g z) t)) ||
    (let eb := bboxE (t :: S) 0
     let bigb : Box := ⟨eb.x0 - 3, eb.x1 + 3, eb.y0 - 3, eb.y1 + 3⟩
     (List.range 8).any fun g => C.all fun z =>
       let w := addC (d4c g z) t
       mem Eg w || deadTestK Sg Eg eb bigb t w)

/-! ## Records and the check of a state -/

/-- The child index that stands for the symbol `∅` (`2^30 - 1`). -/
def NONEK : Nat := 1073741823

/-- The entry of slot `t` (child index `c`, `NONEK` for `∅`) of the state with cells `S`, as `entryOK`. -/
def entryOKK (rd : Nat → Rec) (N : Nat) (S : List Cell) (Sg : Grid) (b1 : Box) (t c : Nat) : Bool :=
  let tc := stepC t
  if c == NONEK then
    mem Sg tc || confinedK Sg (floodK Sg b1 (ox tc.1) (ox tc.2)) b1 (ox tc.1) (ox tc.2)
  else
    decide (c < N) && (mem Sg tc ||
      (let r := rd c
       match decode r.n r.T with
       | none => false
       | some C => childOKK S Sg tc C))

def childVK (rd : Nat → Rec) (c : Nat) : Nat := if c == NONEK then 0 else (rd c).V

/-- The check of state `i`, as `checkState`. -/
def checkStateK (rd : Nat → Rec) (N num den i : Nat) : Bool :=
  let r := rd i
  match decode r.n r.T with
  | none => false
  | some S =>
    let Sg := gridOf S
    let b1 := bboxE S 1
    decide (0 < r.V) &&
      entryOKK rd N S Sg b1 0 r.c0 && entryOKK rd N S Sg b1 1 r.c1 &&
      entryOKK rd N S Sg b1 2 r.c2 &&
      decide (den * (childVK rd r.c0 + childVK rd r.c1 + childVK rd r.c2) ≤ num * r.V)

/-- The states `lo, …, lo + k - 1`. -/
def checkRangeK (rd : Nat → Rec) (N num den lo k : Nat) : Bool :=
  allFrom (checkStateK rd N num den) lo k

/-! ## The data layer: packed records in Braun trees -/

/-- A Braun tree: index `0` at the root, odd indices `2 j + 1` at index `j` of the left subtree, even indices
`2 j + 2` at index `j` of the right subtree. -/
inductive BT (α : Type) where
  | leaf : BT α
  | node : α → BT α → BT α → BT α

/-- The entry at index `i` (`d` if absent). -/
def BT.get {α : Type} (d : α) : BT α → Nat → α
  | .leaf, _ => d
  | .node v l r, i => if i == 0 then v else if i % 2 == 1 then BT.get d l (i / 2) else BT.get d r (i / 2 - 1)

/-- A record of 208 bits: `n` (6 bits), `T` (44), `c₀`, `c₁`, `c₂` (30 each), `V` (62). -/
def recOfK (x : Nat) : Rec :=
  ⟨x &&& 63, (x >>> 6) &&& 17592186044415, (x >>> 50) &&& 1073741823, (x >>> 80) &&& 1073741823,
    (x >>> 110) &&& 1073741823, (x >>> 140) &&& 4611686018427387903⟩

/-- Record `k` of a leaf (records of 208 bits, record `0` in the low bits). -/
def recAt (leaf k : Nat) : Rec := recOfK ((leaf >>> (208 * k)) &&& 411376139330301510538742295639337626245683966408394965837152255)

/-- Record `i` of a two-level table: leaves of `L` records, modules of `P` leaves. -/
def rdT (top : BT (BT Nat)) (L P i : Nat) : Rec :=
  recAt (BT.get 0 (BT.get .leaf top (i / (L * P))) ((i / L) % P)) (i % L)

end Saw38aK

end
