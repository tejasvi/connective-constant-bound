module

public import K30B.Check3b

@[expose] public section


/-!
# Data-layer variants (speedup study): `BT.rec`-based lookups and shard-local module lists
-/

namespace K30B

open Saw38aCore Saw38aK

/-- `BT.get` through the recursor, with `Nat.*` operations (kernel only). -/
noncomputable def btGet {α : Type} (d : α) (t : BT α) : Nat → α :=
  BT.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun v _ _ ihl ihr i => cond (Nat.beq i 0) v
      (cond (Nat.beq (Nat.land i 1) 1) (ihl (Nat.shiftRight i 1)) (ihr (Nat.sub (Nat.shiftRight i 1) 1)))) t

/-- The global table with `btGet`. -/
noncomputable def rdG (top : BT (BT Nat)) (i : Nat) : Rec :=
  recAt30 (btGet 0 (btGet .leaf top (Nat.shiftRight i 20)) (Nat.land (Nat.shiftRight i 6) 16383)) (Nat.land i 63)

/-- The module with number `k` in a shard's list. -/
def findMod (k : Nat) : List (Nat × BT Nat) → BT Nat
  | [] => .leaf
  | m :: ms => cond (Nat.beq m.1 k) m.2 (findMod k ms)

/-- Record `i` from a shard's modules (`BT.get`). -/
def rdK (ms : List (Nat × BT Nat)) (i : Nat) : Rec :=
  recAt30 (BT.get 0 (findMod (Nat.shiftRight i 20) ms) (Nat.land (Nat.shiftRight i 6) 16383)) (Nat.land i 63)

/-- Record `i` from a shard's modules (`btGet`). -/
noncomputable def rdKr (ms : List (Nat × BT Nat)) (i : Nat) : Rec :=
  recAt30 (btGet 0 (findMod (Nat.shiftRight i 20) ms) (Nat.land (Nat.shiftRight i 6) 16383)) (Nat.land i 63)

end K30B

end
