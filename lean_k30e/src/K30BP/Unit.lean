module

public import K30BP.Look

@[expose] public section

/-!
# From a shard unit's public statement to the global table          

`covered_of_coveredL`: if every module listed by a shard is the global module of its number (`ModsOK`, by `rfl` per
module), the unit's hint-free `CoveredL` gives `Covered` for the global two-level table.
-/

namespace K30BP

open Saw38aCore Saw38aK Saw38a K30B

theorem covered_of_coveredL {top : BT (BT Nat)} {ms : List (Nat × BT Nat)} (hok : ModsOK top ms) {N num den lo k : Nat}
    (h : CoveredL ms N num den lo k) : Covered (rdT30 top 64 16384) N num den lo k := by
  intro i hi1 hi2
  obtain ⟨hh, d0, d1, d2, hc⟩ := h i hi1 hi2
  exact ⟨hh, d0, d1, d2, checkState3cL_sound hok hc⟩

theorem modsOK_nil (top : BT (BT Nat)) : ModsOK top [] := by
  intro p hp; simp at hp

/-- One listed module at a time (each `h1` is `rfl` on the global table). -/
theorem modsOK_cons {top : BT (BT Nat)} {k : Nat} {M : BT Nat} {ms : List (Nat × BT Nat)}
    (h1 : BT.get .leaf top k = M) (h2 : ModsOK top ms) : ModsOK top ((k, M) :: ms) := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact h1
  · exact h2 p hp

end K30BP

end
