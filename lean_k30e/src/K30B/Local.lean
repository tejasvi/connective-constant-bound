module

public import K30B.Check3c

@[expose] public section


/-!
# Shard-local data (speedup study): a state's check with its records read from the shard's module list

`checkState3cL ms ...` reads records through `rdKr ms` (the modules imported by the shard) and checks that the state
and each child live in a listed module; `checkRangeL` checks consecutive states with their hints.
-/

namespace K30B

open Saw38aCore Saw38aK

def modIn (k : Nat) : List (Nat × BT Nat) → Bool
  | [] => false
  | m :: ms => Nat.beq m.1 k || modIn k ms

def kidIn (ms : List (Nat × BT Nat)) (c : Nat) : Bool := Nat.beq c NONE30 || modIn (Nat.shiftRight c 20) ms

noncomputable def checkState3cL (ms : List (Nat × BT Nat)) (N num den i hs : Nat) (d0 d1 d2 : List Nat) : Bool :=
  modIn (Nat.shiftRight i 20) ms && kidIn ms (rdKr ms i).c0 && kidIn ms (rdKr ms i).c1 && kidIn ms (rdKr ms i).c2 &&
    checkState3c (rdKr ms) N num den i hs d0 d1 d2

/-- Consecutive states `lo, lo + 1, …` with their hints. -/
noncomputable def checkRangeL (ms : List (Nat × BT Nat)) (N num den : Nat) :
    Nat → List (Nat × List Nat × List Nat × List Nat) → Bool
  | _, [] => true
  | lo, (h, d0, d1, d2) :: hs => checkState3cL ms N num den lo h d0 d1 d2 && checkRangeL ms N num den (lo + 1) hs

/-- The states `lo, …, lo + k - 1` each pass `checkState3cL` against the module list `ms` (with some hints). This is the
public statement of a shard unit: it carries no hints. -/
def CoveredL (ms : List (Nat × BT Nat)) (N num den lo k : Nat) : Prop :=
  ∀ i, lo ≤ i → i < lo + k → ∃ h d0 d1 d2, checkState3cL ms N num den i h d0 d1 d2 = true

theorem coveredL_append {ms : List (Nat × BT Nat)} {N num den lo a b : Nat} (h1 : CoveredL ms N num den lo a)
    (h2 : CoveredL ms N num den (lo + a) b) : CoveredL ms N num den lo (a + b) := by
  intro i hi1 hi2
  by_cases h : i < lo + a
  · exact h1 i hi1 h
  · exact h2 i (by omega) (by omega)

theorem coveredL_of_range (ms : List (Nat × BT Nat)) (N num den : Nat) :
    ∀ (hs : List (Nat × List Nat × List Nat × List Nat)) (lo : Nat), checkRangeL ms N num den lo hs = true →
    CoveredL ms N num den lo hs.length := by
  intro hs
  induction hs with
  | nil => intro lo _ i h1 h2; simp at h2; omega
  | cons x hs ih =>
    intro lo h i h1 h2
    obtain ⟨hh, d0, d1, d2⟩ := x
    simp only [checkRangeL, Bool.and_eq_true] at h
    by_cases e : i = lo
    · subst e; exact ⟨hh, d0, d1, d2, h.1⟩
    · exact ih (lo + 1) h.2 i (by omega) (by simp at h2; omega)

end K30B

end
