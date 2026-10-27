module

public import K30B.Check3a

@[expose] public section


/-!
# Variant 3b (speedup study): packed walks, bitboard no-repeat test, symmetry hints

* Cells are packed `p = 64 y + x` (offset 31); a direction index `0 = +x, 1 = +y, 2 = -x, 3 = -y`; the turn digits are
  read from `T` on the fly; Boolean branching with `cond` and `Nat.beq`, arithmetic with `Nat.*` directly.
* The state's own decode is one walk that checks `small`, tests each new cell against a bitboard (instead of the
  pairwise `nodupO`) and builds the grid and the box on the way.
* A child is walked in the frame of the symmetry `g` given by a hint (`g < 8`; first pass) or `8 + g` (second pass with
  dead-cell tests): the cells of `g(C) + t` come out of the walk directly.
-/

namespace K30B

open Saw38aCore Saw38aK

def stepBackP (i p : Nat) : Nat :=
  cond (Nat.beq i 0) (Nat.sub p 1) (cond (Nat.beq i 1) (Nat.sub p 64) (cond (Nat.beq i 2) (Nat.add p 1) (Nat.add p 64)))

def turnP (t i : Nat) : Nat :=
  cond (Nat.beq t 1) (Nat.mod (Nat.add i 3) 4) (cond (Nat.beq t 2) (Nat.mod (Nat.add i 1) 4) i)

/-- Bit `p` of the bitboard `B`. -/
def bitP (B p : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight B p) 1) 1

/-- `small` for a packed cell (offset 31: both coordinates in `[3, 59]`). -/
def smallP (p : Nat) : Bool :=
  let x := Nat.land p 63
  let y := Nat.shiftRight p 6
  Nat.ble 3 x && Nat.ble x 59 && Nat.ble 3 y && Nat.ble y 59

/-- The own walk: `k` more digits of `T`, direction `i`, current first cell `p`, bitboard `B`, box `x0 x1 y0 y1`.
Returns the bitboard and the box, or `none` (a cell outside `small`, a repeated cell, or excess digits). -/
def ownWalk : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Option (Nat × Box)
  | 0, T, _, _, B, x0, x1, y0, y1 => cond (Nat.beq T 0) (some (B, ⟨x0, x1, y0, y1⟩)) none
  | k + 1, T, i, p, B, x0, x1, y0, y1 =>
    let i' := turnP (Nat.mod T 3) i
    let p' := stepBackP i' p
    let x := Nat.land p' 63
    let y := Nat.shiftRight p' 6
    cond (smallP p' && !bitP B p')
      (ownWalk k (Nat.div T 3) i' p' (Nat.lor B (Nat.shiftLeft 1 p')) (Nat.min x0 x) (Nat.max x1 x) (Nat.min y0 y)
        (Nat.max y1 y))
      none

/-- The state's decode, grid and box (cells `(30, 31)`, `(31, 31)` first). -/
def ownDec (n T : Nat) : Option (Nat × Box) :=
  cond (Nat.blt n 2 || Nat.blt 40 n) none
    (ownWalk (n - 2) T 0 2014 (Nat.lor (Nat.shiftLeft 1 2014) (Nat.shiftLeft 1 2015)) 30 31 31 31)

/-- The direction index `g(e_i)` and whether `g` reverses orientation. -/
def gdir (g i : Nat) : Nat :=
  cond (Nat.blt g 4) (Nat.mod (Nat.add i g) 4)
    (Nat.mod (Nat.sub (Nat.add (cond (Nat.beq g 4) 0 (cond (Nat.beq g 5) 2 (cond (Nat.beq g 6) 1 3))) 4) i) 4)

def swapT (sw : Bool) (t : Nat) : Nat := cond sw (cond (Nat.beq t 1) 2 (cond (Nat.beq t 2) 1 t)) t

/-- First pass in the frame of `g`: every cell of the walk is in `Eg` (`k` digits of `T` left). -/
def walkIn (Eg : Nat) (sw : Bool) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => true
  | k + 1, T, i, p =>
    let i' := turnP (swapT sw (Nat.mod T 3)) i
    let p' := stepBackP i' p
    bitP Eg p' && walkIn Eg sw k (Nat.div T 3) i' p'

/-- Second pass in the frame of `g`: every cell is in `Eg` or dead (`deadTestB2`). -/
def walkDead (Sg Eg : Nat) (bigb : Box) (t : Nat × Nat) (sw : Bool) : Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _ => true
  | k + 1, T, i, p =>
    let i' := turnP (swapT sw (Nat.mod T 3)) i
    let p' := stepBackP i' p
    (bitP Eg p' || deadTestB2 Sg Eg bigb t (Nat.land p' 63, Nat.shiftRight p' 6)) &&
      walkDead Sg Eg bigb t sw k (Nat.div T 3) i' p'

def tcP (t : Nat) : Nat := cond (Nat.beq t 0) 2016 (cond (Nat.beq t 1) 2079 1951)

/-- The child test with hint `h` (`g` or `8 + g`): the child's cells `C` under `g`, placed at the target `tc`. -/
def childOK3b (Sg : Nat) (bb : Box) (t : Nat) (r : Rec) (h : Nat) : Bool :=
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
     (bitP Eg p1 || deadTestB2 Sg Eg bigb (tx, ty) (Nat.land p1 63, Nat.shiftRight p1 6)) &&
       walkDead Sg Eg bigb (tx, ty) sw (r.n - 2) r.T d0 p1)

def entryOK3b (rd : Nat → Rec) (N : Nat) (Sg : Nat) (bb b1 : Box) (t c h : Nat) : Bool :=
  let tc := tcP t
  cond (Nat.beq c NONE30)
    (bitP Sg tc || confinedB Sg (floodB Sg b1 (Nat.land tc 63) (Nat.shiftRight tc 6)) b1 (Nat.land tc 63) (Nat.shiftRight tc 6))
    (Nat.blt c N && (bitP Sg tc || childOK3b Sg bb t (rd c) h))

/-- The check of state `i` with the slot hints `hs = h₀ + 16 h₁ + 256 h₂`. -/
def checkState3b (rd : Nat → Rec) (N num den i hs : Nat) : Bool :=
  let r := rd i
  match ownDec r.n r.T with
  | none => false
  | some (Sg, bb) =>
    let b1 : Box := ⟨bb.x0 - 1, bb.x1 + 1, bb.y0 - 1, bb.y1 + 1⟩
    Nat.blt 0 r.V &&
      entryOK3b rd N Sg bb b1 0 r.c0 (Nat.mod hs 16) && entryOK3b rd N Sg bb b1 1 r.c1 (Nat.mod (Nat.div hs 16) 16) &&
      entryOK3b rd N Sg bb b1 2 r.c2 (Nat.div hs 256) &&
      Nat.ble (Nat.mul den (Nat.add (Nat.add (childV30 rd r.c0) (childV30 rd r.c1)) (childV30 rd r.c2))) (Nat.mul num r.V)

/-- States with hints, as a list of pairs. -/
def checkListH3b (rd : Nat → Rec) (N num den : Nat) : List (Nat × Nat) → Bool
  | [] => true
  | (i, h) :: is => checkState3b rd N num den i h && checkListH3b rd N num den is

/-! ## Hints (compiled, untrusted) -/

/-- The hint of slot `t` (16 if none is needed or none works). -/
def hintSlot (rd : Nat → Rec) (N : Nat) (i t : Nat) : Nat :=
  let r := rd i
  let c := cond (Nat.beq t 0) r.c0 (cond (Nat.beq t 1) r.c1 r.c2)
  match ownDec r.n r.T with
  | none => 15
  | some (Sg, bb) =>
    if c == NONE30 || bitP Sg (tcP t) then 0 else
    let rc := rd c
    match (List.range 16).find? (fun h => childOK3b Sg bb t rc h) with
    | some h => h
    | none => 15

def hintState (rd : Nat → Rec) (N i : Nat) : Nat :=
  hintSlot rd N i 0 + 16 * hintSlot rd N i 1 + 256 * hintSlot rd N i 2

end K30B

end
