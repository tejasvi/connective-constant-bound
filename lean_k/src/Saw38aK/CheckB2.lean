import Saw38aK.CheckB

/-!
# Bitboard checker, version 2: dead-cell tests on bitboards

As `checkStateB`, with the rare paths on bitboards too:

* `closedB` checks the closure of a region with whole-grid bit operations: the region's cells in the box lie strictly
  inside it, and every neighbour of one of them is blocked or in the region. `Saw38aKP/BridgeB2.lean` proves that it
  implies the audited `closedIn` on the grids of the bitboards (`toGrid`).
* `confinedB`, `nbCountB`, `tNbrsOKB`, `testCB`, `deadTestB2`, `childOKB2`, `entryOKB2`, `checkStateB2` follow the audited
  `confined`, `nbCount`, `tNbrsOK`, `testC`, `deadTest`, `childOK`, `entryOK`, `checkState`, on offset cells.
* `floodB`, `pathToRingB` and `candsB` are untrusted helpers (no proof obligation): every claim they suggest is
  re-checked by `confinedB` or `testCB`.
-/

namespace Saw38aK

open Saw38aCore

/-! ## Masks -/

/-- The bits `x0..min x1 62` of a row (none if `x0 > min x1 62`). -/
def maskC (x0 x1 : Nat) : Nat := if x0 ≤ min x1 62 then (2 ^ (min x1 62 + 1 - x0) - 1) <<< x0 else 0

/-- The row mask `m` repeated on the rows `r, …, r + k - 1`. -/
def maskRows (m : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | r, k + 1 => (m <<< (64 * r)) ||| maskRows m (r + 1) k

/-- The cells `x0..x1 × y0..y1` (clipped to `[0, 62]²`). -/
def boxMaskB (b : Box) : Nat := maskRows (maskC b.x0 b.x1) b.y0 (min b.y1 62 + 1 - b.y0)

/-- The cells strictly inside the box (`x0 < x < x1`, `y0 < y < y1`, clipped to `[0, 62]²`). -/
def innerMaskB (b : Box) : Nat := maskRows (maskC (b.x0 + 1) (b.x1 - 1)) (b.y0 + 1) (min (b.y1 - 1) 62 + 1 - (b.y0 + 1))

/-! ## Closure and confinement (checked) -/

/-- The cells of `R` in the box lie strictly inside it, and each neighbour of such a cell is in `blk` or `R`. -/
def closedB (blk R : Nat) (b : Box) : Bool :=
  let Rb := R &&& boxMaskB b
  let nb := (Rb <<< 1) ||| (Rb >>> 1) ||| (Rb <<< 64) ||| (Rb >>> 64)
  (Rb &&& innerMaskB b == Rb) && (nb &&& (blk ||| R) == nb)

/-- `R` contains `(x, y)` and is closed in the box: `(x, y)` cannot leave the box avoiding `blk` (as `confined`). -/
def confinedB (blk R : Nat) (b : Box) (x y : Nat) : Bool :=
  b.x1 ≤ 62 && b.y1 ≤ 62 && b.x0 ≤ x && x ≤ b.x1 && b.y0 ≤ y && y ≤ b.y1 && memB R x y && closedB blk R b

/-! ## Untrusted helpers on bitboards -/

/-- 4-connected flood fill from `(sx, sy)` over the cells of the box that are not blocked. -/
def floodB (blk : Nat) (bx : Box) (sx sy : Nat) : Nat :=
  let bm := boxMaskB bx
  let free := bm ^^^ (blk &&& bm)
  let s := 64 * sy + sx
  if sx > 62 || (free >>> s) &&& 1 == 0 then 0 else floodBB free 4096 (2 ^ s)

/-- The position of the single set bit of `b` (binary search over 12 levels). -/
def bitPos (b : Nat) : Nat → Nat → Nat
  | 0, p => p
  | j + 1, p => if (b >>> (p + 2 ^ j)) != 0 then bitPos b j (p + 2 ^ j) else bitPos b j p

/-- Cells after the first on one shortest 4-connected path from `(x, y)` through cells of `fl` to the ring of the box
(the start excluded, the ring cell included). -/
def pathToRingB (fl : Nat) (bx : Box) (x y : Nat) : Array (Nat × Nat) :=
  let ring := ringBB bx 63 0 0
  let s := 2 ^ (64 * y + x)
  if s &&& ring != 0 then #[]
  else
    match layersBB fl ring 4096 s [s] with
    | (top :: rest, true) =>
      let h := top &&& ring
      let g := bitPos (h ^^^ (h &&& (h - 1))) 12 0
      (backBB rest g [(g % 64, g / 64)]).toArray
    | _ => #[]

/-- Candidates for the cell `w` of test (c), as `cands`. -/
def candsB (Eg : Nat) (fl : Nat) (bigb : Box) (x y : Nat) : Array (Nat × Nat) :=
  (pathToRingB fl bigb x y).filter fun c =>
    let xx := c.1
    let yy := c.2
    xx ≥ 1 && yy ≥ 1 && !memB Eg xx yy &&
      (((Eg >>> (64 * (yy - 1))) ||| (Eg >>> (64 * yy)) ||| (Eg >>> (64 * (yy + 1)))) >>> (xx - 1)) &&& 7 != 0

/-! ## Dead cells, children, entries, states (checked) -/

/-- The number of neighbours of the offset cell `z` in `g` (as `nbCount`). -/
def nbCountB (g : Nat) (z : Nat × Nat) : Nat :=
  (if memB g (z.1 + 1) z.2 then 1 else 0) + (if memB g (z.1 - 1) z.2 then 1 else 0) +
  (if memB g z.1 (z.2 + 1) then 1 else 0) + (if memB g z.1 (z.2 - 1) then 1 else 0)

/-- No neighbour of `t` outside `blk` lies in `R` (as `tNbrsOK`). -/
def tNbrsOKB (blk R : Nat) (t : Nat × Nat) : Bool :=
  (memB blk (t.1 + 1) t.2 || !memB R (t.1 + 1) t.2) && (memB blk (t.1 - 1) t.2 || !memB R (t.1 - 1) t.2) &&
  (memB blk t.1 (t.2 + 1) || !memB R t.1 (t.2 + 1)) && (memB blk t.1 (t.2 - 1) || !memB R t.1 (t.2 - 1))

/-- Test (c) for the cell `(wx, wy)` (as `testC`). -/
def testCB (Eg : Nat) (bigb : Box) (t : Nat × Nat) (x y wx wy : Nat) : Bool :=
  let Bw := setB Eg wx wy
  let f2 := floodB Bw bigb x y
  wx ≤ 62 && wy ≤ 62 && !memB Eg wx wy && !(wx == x && wy == y) && confinedB Bw f2 bigb x y && tNbrsOKB Bw f2 t

/-- The offset cell `w` (outside `E`) is dead for `(S, t)` (as `deadTest`). -/
def deadTestB2 (Sg Eg : Nat) (bigb : Box) (t w : Nat × Nat) : Bool :=
  (w.1 ≤ 62 && w.2 ≤ 62) &&
    (decide (3 ≤ nbCountB Sg w) ||
      (let fl := floodB Eg bigb w.1 w.2
       confinedB Eg fl bigb w.1 w.2 ||
         (bigb.x0 < w.1 && w.1 < bigb.x1 && bigb.y0 < w.2 && w.2 < bigb.y1 &&
           (candsB Eg fl bigb w.1 w.2).any fun c => testCB Eg bigb t w.1 w.2 c.1 c.2)))

/-- (C2) for the child with offset cells `C` (as `childOK`). -/
def childOKB2 (S : List (Nat × Nat)) (Sg : Nat) (t : Nat × Nat) (C : List (Nat × Nat)) : Bool :=
  let Eg := setB Sg t.1 t.2
  (List.range 8).any (fun g => C.all fun z => memO Eg (addO (d4o g z) t)) ||
    (let eb := bboxO (t :: S) 0
     let bigb : Box := ⟨eb.x0 - 3, eb.x1 + 3, eb.y0 - 3, eb.y1 + 3⟩
     (List.range 8).any fun g => C.all fun z =>
       let w := addO (d4o g z) t
       memO Eg w || deadTestB2 Sg Eg bigb t w)

/-- The entry of slot `t` (child index `c`) (as `entryOK`). -/
def entryOKB2 (rd : Nat → Rec) (N : Nat) (S : List (Nat × Nat)) (Sg : Nat) (b1 : Box) (t c : Nat) : Bool :=
  let tc := stepO t
  if c == NONEK then
    memO Sg tc || confinedB Sg (floodB Sg b1 tc.1 tc.2) b1 tc.1 tc.2
  else
    decide (c < N) && (memO Sg tc ||
      (let r := rd c
       match decodeO r.n r.T with
       | none => false
       | some C => childOKB2 S Sg tc C))

/-- The check of state `i` (as `checkState`). -/
def checkStateB2 (rd : Nat → Rec) (N num den i : Nat) : Bool :=
  let r := rd i
  match decodeO r.n r.T with
  | none => false
  | some S =>
    let Sg := gridB S
    let b1 := bboxO S 1
    decide (0 < r.V) &&
      entryOKB2 rd N S Sg b1 0 r.c0 && entryOKB2 rd N S Sg b1 1 r.c1 &&
      entryOKB2 rd N S Sg b1 2 r.c2 &&
      decide (den * (childVK rd r.c0 + childVK rd r.c1 + childVK rd r.c2) ≤ num * r.V)

/-- The states `lo, …, lo + k - 1`. -/
def checkRangeB2 (rd : Nat → Rec) (N num den lo k : Nat) : Bool :=
  allFrom (checkStateB2 rd N num den) lo k

end Saw38aK
