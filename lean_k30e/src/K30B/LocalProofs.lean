module

public import K30B.Local

@[expose] public section

/-!
# Shard-local reads equal the global table (core Lean)         

The same statements as `K30BP/Look.lean` and `K30BP/Unit.lean` (`btGet_eq`, `findMod_ok`, `rdKr_eq`,
`checkState3c_congr`, `checkState3cL_sound`, `covered_of_coveredL`), proved without Mathlib so that part modules
can be module files: a part imports its units privately and exports only `CoveredG` for the global table, so the root's
import closure holds parts, the data modules and the library, not the ~500k units.
-/

namespace K30B

open Saw38aCore Saw38aK

/-- As `K30BP.Covered` (same body): the states `lo, …, lo + k - 1` each pass `checkState3c` (with some hints). -/
def CoveredG (rd : Nat → Rec) (N num den lo k : Nat) : Prop :=
  ∀ i, lo ≤ i → i < lo + k → ∃ h d0 d1 d2, checkState3c rd N num den i h d0 d1 d2 = true

theorem coveredG_append {rd : Nat → Rec} {N num den lo a b : Nat} (h1 : CoveredG rd N num den lo a)
    (h2 : CoveredG rd N num den (lo + a) b) : CoveredG rd N num den lo (a + b) := by
  intro i hi1 hi2
  by_cases h : i < lo + a
  · exact h1 i hi1 h
  · exact h2 i (by omega) (by omega)

/-- As `K30BP.ModsOK`: every listed module is the global module of its number. -/
def ModsOKG (top : BT (BT Nat)) (ms : List (Nat × BT Nat)) : Prop := ∀ p ∈ ms, BT.get .leaf top p.1 = p.2

theorem modsOKG_nil (top : BT (BT Nat)) : ModsOKG top [] := by
  intro p hp; simp at hp

theorem modsOKG_cons {top : BT (BT Nat)} {k : Nat} {M : BT Nat} {ms : List (Nat × BT Nat)}
    (h1 : BT.get .leaf top k = M) (h2 : ModsOKG top ms) : ModsOKG top ((k, M) :: ms) := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · exact h1
  · exact h2 p hp

theorem btGet_eqG {α : Type} (d : α) (t : BT α) : ∀ i, btGet d t i = BT.get d t i := by
  induction t with
  | leaf => intro i; rfl
  | node v l r ihl ihr =>
    intro i
    have e1 : btGet d (BT.node v l r) i = cond (Nat.beq i 0) v
        (cond (Nat.beq (Nat.land i 1) 1) (btGet d l (Nat.shiftRight i 1)) (btGet d r (Nat.sub (Nat.shiftRight i 1) 1))) := rfl
    have h1 : Nat.land i 1 = i % 2 := Nat.and_one_is_mod i
    have h2 : Nat.shiftRight i 1 = i / 2 := Nat.shiftRight_eq_div_pow i 1
    rw [e1, h1, h2, ihl, ihr]
    simp only [BT.get]
    by_cases h0 : i = 0
    · subst h0; rfl
    · have hb : Nat.beq i 0 = false := by
        cases h' : Nat.beq i 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h') h0
      have hb' : (i == 0) = false := by simpa using h0
      rw [hb, hb']
      rcases Nat.mod_two_eq_zero_or_one i with hm | hm
      · rw [hm]; rfl
      · rw [hm]; rfl

theorem findMod_okG {top : BT (BT Nat)} : ∀ {ms : List (Nat × BT Nat)} {k : Nat}, ModsOKG top ms → modIn k ms = true →
    findMod k ms = BT.get .leaf top k := by
  intro ms
  induction ms with
  | nil => intro k _ h; simp [modIn] at h
  | cons m ms ih =>
    intro k hok h
    simp only [modIn, Bool.or_eq_true] at h
    simp only [findMod]
    cases hb : Nat.beq m.1 k with
    | true =>
      have e := Nat.eq_of_beq_eq_true hb
      simp only [Bool.cond_true]
      rw [← e]; exact (hok m List.mem_cons_self).symm
    | false =>
      simp only [Bool.cond_false]
      rw [hb] at h
      simp only [Bool.false_eq_true, false_or] at h
      exact ih (fun p hp => hok p (List.mem_cons_of_mem _ hp)) h

theorem rdKr_eqG {top : BT (BT Nat)} {ms : List (Nat × BT Nat)} (hok : ModsOKG top ms) {i : Nat}
    (hi : modIn (Nat.shiftRight i 20) ms = true) : rdKr ms i = rdT30 top 64 16384 i := by
  unfold rdKr rdT30
  rw [btGet_eqG, findMod_okG hok hi]
  have e1 : Nat.shiftRight i 20 = i / (64 * 16384) := Nat.shiftRight_eq_div_pow i 20
  have e2 : Nat.land (Nat.shiftRight i 6) 16383 = i / 64 % 16384 := by
    have h6 : Nat.shiftRight i 6 = i / 2 ^ 6 := Nat.shiftRight_eq_div_pow i 6
    have hm : Nat.land (i / 2 ^ 6) 16383 = (i / 2 ^ 6) &&& (2 ^ 14 - 1) := rfl
    rw [h6, hm, Nat.and_two_pow_sub_one_eq_mod]
  have e3 : Nat.land i 63 = i % 64 := by
    have hm : Nat.land i 63 = i &&& (2 ^ 6 - 1) := rfl
    rw [hm, Nat.and_two_pow_sub_one_eq_mod]
  rw [e1, e2, e3]

theorem checkState3c_congrG {rd rd' : Nat → Rec} {N num den i hs : Nat} {d0 d1 d2 : List Nat} (hi : rd' i = rd i)
    (h0 : (rd i).c0 ≠ NONE30 → rd' (rd i).c0 = rd (rd i).c0) (h1 : (rd i).c1 ≠ NONE30 → rd' (rd i).c1 = rd (rd i).c1)
    (h2 : (rd i).c2 ≠ NONE30 → rd' (rd i).c2 = rd (rd i).c2) :
    checkState3c rd' N num den i hs d0 d1 d2 = checkState3c rd N num den i hs d0 d1 d2 := by
  have hent : ∀ (Sg : Nat) (bb b1 : Box) (t c h : Nat) (dh : List Nat), (c ≠ NONE30 → rd' c = rd c) →
      entryOK3c rd' N Sg bb b1 t c h dh = entryOK3c rd N Sg bb b1 t c h dh := by
    intro Sg bb b1 t c h dh hc
    by_cases e : c = NONE30
    · subst e; simp [entryOK3c]
    · simp only [entryOK3c, hc e]
  have hv : ∀ c, (c ≠ NONE30 → rd' c = rd c) → childV30 rd' c = childV30 rd c := by
    intro c hc
    by_cases e : c = NONE30
    · subst e; simp [childV30]
    · simp only [childV30, hc e]
  unfold checkState3c
  rw [hi]
  dsimp only
  cases hd : ownDec (rd i).n (rd i).T with
  | none => rfl
  | some x =>
    obtain ⟨Sg, bb⟩ := x
    dsimp only
    rw [hent _ _ _ _ _ _ _ h0, hent _ _ _ _ _ _ _ h1, hent _ _ _ _ _ _ _ h2, hv _ h0, hv _ h1, hv _ h2]

theorem checkState3cL_soundG {top : BT (BT Nat)} {ms : List (Nat × BT Nat)} (hok : ModsOKG top ms)
    {N num den i hs : Nat} {d0 d1 d2 : List Nat} (h : checkState3cL ms N num den i hs d0 d1 d2 = true) :
    checkState3c (rdT30 top 64 16384) N num den i hs d0 d1 d2 = true := by
  have kid : ∀ {c : Nat}, kidIn ms c = true → c ≠ NONE30 → modIn (Nat.shiftRight c 20) ms = true := by
    intro c hk hc
    simp only [kidIn, Bool.or_eq_true] at hk
    rcases hk with hk | hk
    · exact absurd (Nat.eq_of_beq_eq_true hk) hc
    · exact hk
  simp only [checkState3cL, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hi, k0⟩, k1⟩, k2⟩, hc⟩ := h
  have ei : rdKr ms i = rdT30 top 64 16384 i := rdKr_eqG hok hi
  rw [ei] at k0 k1 k2
  rw [← checkState3c_congrG (rd' := rdKr ms) ei (fun hc0 => rdKr_eqG hok (kid k0 hc0))
    (fun hc1 => rdKr_eqG hok (kid k1 hc1)) (fun hc2 => rdKr_eqG hok (kid k2 hc2))]
  exact hc

/-- A shard unit's hint-free statement gives `CoveredG` on the global table. -/
theorem coveredG_of_coveredL {top : BT (BT Nat)} {ms : List (Nat × BT Nat)} (hok : ModsOKG top ms)
    {N num den lo k : Nat} (h : CoveredL ms N num den lo k) : CoveredG (rdT30 top 64 16384) N num den lo k := by
  intro i hi1 hi2
  obtain ⟨hh, d0, d1, d2, hc⟩ := h i hi1 hi2
  exact ⟨hh, d0, d1, d2, checkState3cL_soundG hok hc⟩

end K30B

end
