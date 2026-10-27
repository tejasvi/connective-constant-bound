module

public import K30B.Look

@[expose] public section


/-!
# Variant 3c (speedup study): 3b plus dead-cell hints

For a second-pass slot, each child cell outside `E` carries a hint: `0` = test (a) (three neighbours), `1` = test (b)
(the flood region is closed), `2 + q` = test (c) with the cut cell `q` (packed). The soundness proof of `deadTestB2`
already uses only the test that succeeds and, for (c), only `testCB` of the found cell (not its membership in
`candsB`), so a hinted test is sound by the same argument.
-/

namespace K30B

open Saw38aCore Saw38aK

/-- The hinted dead-cell test of the packed cell `p`. -/
def deadH (Sg Eg : Nat) (bigb : Box) (t : Nat × Nat) (p h : Nat) : Bool :=
  let x := Nat.land p 63
  let y := Nat.shiftRight p 6
  Nat.ble x 62 && Nat.ble y 62 &&
    cond (Nat.beq h 0) (Nat.ble 3 (nbCountB Sg (x, y)))
      (cond (Nat.beq h 1) (confinedB Eg (floodB Eg bigb x y) bigb x y)
        (Nat.blt bigb.x0 x && Nat.blt x bigb.x1 && Nat.blt bigb.y0 y && Nat.blt y bigb.y1 &&
          testCB Eg bigb t x y (Nat.land (h - 2) 63) (Nat.shiftRight (h - 2) 6)))

/-- Second pass in the frame of `g` with dead-cell hints (one per cell outside `E`, in walk order). -/
def walkDeadH (Sg Eg : Nat) (bigb : Box) (t : Nat × Nat) (sw : Bool) : Nat → Nat → Nat → Nat → List Nat → Bool
  | 0, _, _, _, _ => true
  | k + 1, T, i, p, hs =>
    let i' := turnP (swapT sw (Nat.mod T 3)) i
    let p' := stepBackP i' p
    cond (bitP Eg p') (walkDeadH Sg Eg bigb t sw k (Nat.div T 3) i' p' hs)
      (match hs with
       | [] => false
       | h :: hs' => deadH Sg Eg bigb t p' h && walkDeadH Sg Eg bigb t sw k (Nat.div T 3) i' p' hs')

def childOK3c (Sg : Nat) (bb : Box) (t : Nat) (r : Rec) (h : Nat) (dh : List Nat) : Bool :=
  let tc := tcP t
  let Eg := Nat.lor Sg (Nat.shiftLeft 1 tc)
  let g := Nat.mod h 8
  let sw := Nat.ble 4 g
  let d0 := gdir g 0
  let p1 := stepBackP d0 tc
  cond (Nat.blt h 8)
    (bitP Eg p1 && walkIn Eg sw (r.n - 2) r.T d0 p1)
    (let tx := Nat.land tc 63
     let ty := Nat.shiftRight tc 6
     let bigb : Box := ⟨Nat.min bb.x0 tx - 3, Nat.max bb.x1 tx + 3, Nat.min bb.y0 ty - 3, Nat.max bb.y1 ty + 3⟩
     cond (bitP Eg p1) (walkDeadH Sg Eg bigb (tx, ty) sw (r.n - 2) r.T d0 p1 dh)
       (match dh with
        | [] => false
        | q :: dh' => deadH Sg Eg bigb (tx, ty) p1 q && walkDeadH Sg Eg bigb (tx, ty) sw (r.n - 2) r.T d0 p1 dh'))

def entryOK3c (rd : Nat → Rec) (N : Nat) (Sg : Nat) (bb b1 : Box) (t c h : Nat) (dh : List Nat) : Bool :=
  let tc := tcP t
  cond (Nat.beq c NONE30)
    (bitP Sg tc || confinedB Sg (floodB Sg b1 (Nat.land tc 63) (Nat.shiftRight tc 6)) b1 (Nat.land tc 63) (Nat.shiftRight tc 6))
    (Nat.blt c N && (bitP Sg tc || childOK3c Sg bb t (rd c) h dh))

/-- The check of state `i` with slot hints `hs` and dead-cell hints `d₀ d₁ d₂`. -/
def checkState3c (rd : Nat → Rec) (N num den i hs : Nat) (d0 d1 d2 : List Nat) : Bool :=
  let r := rd i
  match ownDec r.n r.T with
  | none => false
  | some (Sg, bb) =>
    let b1 : Box := ⟨bb.x0 - 1, bb.x1 + 1, bb.y0 - 1, bb.y1 + 1⟩
    Nat.blt 0 r.V &&
      entryOK3c rd N Sg bb b1 0 r.c0 (Nat.mod hs 16) d0 && entryOK3c rd N Sg bb b1 1 r.c1 (Nat.mod (Nat.div hs 16) 16) d1 &&
      entryOK3c rd N Sg bb b1 2 r.c2 (Nat.div hs 256) d2 &&
      Nat.ble (Nat.mul den (Nat.add (Nat.add (childV30 rd r.c0) (childV30 rd r.c1)) (childV30 rd r.c2))) (Nat.mul num r.V)

def checkListH3c (rd : Nat → Rec) (N num den : Nat) : List (Nat × Nat × List Nat × List Nat × List Nat) → Bool
  | [] => true
  | (i, h, d0, d1, d2) :: is => checkState3c rd N num den i h d0 d1 d2 && checkListH3c rd N num den is

/-! ## Dead-cell hints (compiled, untrusted) -/

/-- The hint of the packed cell `p` (as `deadTestB2` decides it), or none. -/
def deadHint (Sg Eg : Nat) (bigb : Box) (t : Nat × Nat) (p : Nat) : Option Nat :=
  let x := Nat.land p 63
  let y := Nat.shiftRight p 6
  if 3 ≤ nbCountB Sg (x, y) then some 0
  else if confinedB Eg (floodB Eg bigb x y) bigb x y then some 1
  else match (candsB Eg (floodB Eg bigb x y) bigb x y).find? (fun c => testCB Eg bigb t x y c.1 c.2) with
    | some c => some (2 + 64 * c.2 + c.1)
    | none => none

/-- The cells of the walk in the frame of `g` (first cell `p1` first). -/
def walkCells (sw : Bool) : Nat → Nat → Nat → Nat → List Nat
  | 0, _, _, _ => []
  | k + 1, T, i, p =>
    let i' := turnP (swapT sw (Nat.mod T 3)) i
    let p' := stepBackP i' p
    p' :: walkCells sw k (Nat.div T 3) i' p'

/-- The dead-cell hints of slot `t` with slot hint `h` (empty unless `h ≥ 8`). -/
def deadHints (rd : Nat → Rec) (i t h : Nat) : List Nat :=
  if h < 8 || h ≥ 16 then [] else
  let r := rd i
  let c := cond (Nat.beq t 0) r.c0 (cond (Nat.beq t 1) r.c1 r.c2)
  match ownDec r.n r.T with
  | none => []
  | some (Sg, bb) =>
    let rc := rd c
    let tc := tcP t
    let Eg := Nat.lor Sg (Nat.shiftLeft 1 tc)
    let g := h % 8
    let d0 := gdir g 0
    let p1 := stepBackP d0 tc
    let tx := Nat.land tc 63
    let ty := Nat.shiftRight tc 6
    let bigb : Box := ⟨Nat.min bb.x0 tx - 3, Nat.max bb.x1 tx + 3, Nat.min bb.y0 ty - 3, Nat.max bb.y1 ty + 3⟩
    ((p1 :: walkCells (Nat.ble 4 g) (rc.n - 2) rc.T d0 p1).filter (fun p => !bitP Eg p)).map fun p =>
      (deadHint Sg Eg bigb (tx, ty) p).getD 1000000

end K30B

end
