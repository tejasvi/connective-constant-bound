import Saw38aK.CheckB2

/-!
# Adjacent ranges of checked states (core Lean only)

Shard, part and root modules combine their range checks with `checkRangeB2_append'`; they need neither Mathlib nor
the soundness proofs.
-/

namespace Saw38aK

open Saw38aCore

theorem allFrom_append (p : Nat → Bool) : ∀ (i a b : Nat), allFrom p i a = true → allFrom p (i + a) b = true →
    allFrom p i (a + b) = true := by
  intro i a
  induction a generalizing i with
  | zero => intro b _ h; simpa using h
  | succ a ih =>
    intro b h1 h2
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [allFrom, Bool.and_eq_true] at h1 ⊢
    exact ⟨h1.1, ih (i + 1) b h1.2 (by rw [show i + 1 + a = i + (a + 1) by omega]; exact h2)⟩

/-- Two adjacent ranges of checked states. -/
theorem checkRangeB2_append' {rd : Nat → Rec} {N num den lo a b : Nat} (h1 : checkRangeB2 rd N num den lo a = true)
    (h2 : checkRangeB2 rd N num den (lo + a) b = true) : checkRangeB2 rd N num den lo (a + b) = true :=
  allFrom_append _ lo a b h1 h2

end Saw38aK
