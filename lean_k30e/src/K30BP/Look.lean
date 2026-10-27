module

public import K30BP.Main3c
public import K30B.Local

@[expose] public section

/-!
# Soundness of the data layer (speedup study)         

* `btGet_eq`: the recursor-based lookup is `BT.get`.
* `rdKr_eq`: a record read from a shard's module list equals the record of the global two-level table, when every
  listed module is the global one (`ModsOK`) and the record's module is listed.
* `checkState3cL_sound`: a shard-local check gives the check against the global table.
* `Covered`: the per-range statement the shards and parts combine (`covered_append`); `checkRangeL_covered`.
-/

namespace K30BP

open Saw38aCore Saw38aK Saw38a K30B

theorem btGet_eq {α : Type} (d : α) (t : BT α) : ∀ i, btGet d t i = BT.get d t i := by
  induction t with
  | leaf => intro i; rfl
  | node v l r ihl ihr =>
    intro i
    have e1 : btGet d (BT.node v l r) i = cond (Nat.beq i 0) v
        (cond (Nat.beq (Nat.land i 1) 1) (btGet d l (Nat.shiftRight i 1)) (btGet d r (Nat.sub (Nat.shiftRight i 1) 1))) := rfl
    have h1 : Nat.land i 1 = i % 2 := Nat.and_one_is_mod i
    have h2 : Nat.shiftRight i 1 = i / 2 := by
      have : Nat.shiftRight i 1 = i / 2 ^ 1 := Nat.shiftRight_eq_div_pow i 1
      rw [this]; norm_num
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

/-- Every listed module is the global module of its number. -/
def ModsOK (top : BT (BT Nat)) (ms : List (Nat × BT Nat)) : Prop := ∀ p ∈ ms, BT.get .leaf top p.1 = p.2

theorem findMod_ok {top : BT (BT Nat)} : ∀ {ms : List (Nat × BT Nat)} {k : Nat}, ModsOK top ms → modIn k ms = true →
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

theorem rdKr_eq {top : BT (BT Nat)} {ms : List (Nat × BT Nat)} (hok : ModsOK top ms) {i : Nat}
    (hi : modIn (Nat.shiftRight i 20) ms = true) : rdKr ms i = rdT30 top 64 16384 i := by
  unfold rdKr rdT30
  rw [btGet_eq, findMod_ok hok hi]
  have e1 : Nat.shiftRight i 20 = i / (64 * 16384) := by
    have : Nat.shiftRight i 20 = i / 2 ^ 20 := Nat.shiftRight_eq_div_pow i 20
    rw [this]; norm_num
  have e2 : Nat.land (Nat.shiftRight i 6) 16383 = i / 64 % 16384 := by
    have h6 : Nat.shiftRight i 6 = i / 2 ^ 6 := Nat.shiftRight_eq_div_pow i 6
    have hm : Nat.land (i / 2 ^ 6) 16383 = (i / 2 ^ 6) &&& (2 ^ 14 - 1) := rfl
    rw [h6, hm, Nat.and_two_pow_sub_one_eq_mod]; norm_num
  have e3 : Nat.land i 63 = i % 64 := land63 i
  rw [e1, e2, e3]

/-- `checkState3c` reads `rd` only at the state and at its children. -/
theorem checkState3c_congr {rd rd' : Nat → Rec} {N num den i hs : Nat} {d0 d1 d2 : List Nat} (hi : rd' i = rd i)
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

theorem modIn_of_kidIn {ms : List (Nat × BT Nat)} {c : Nat} (h : kidIn ms c = true) (hc : c ≠ NONE30) :
    modIn (Nat.shiftRight c 20) ms = true := by
  simp only [kidIn, Bool.or_eq_true] at h
  rcases h with h | h
  · exact absurd (Nat.eq_of_beq_eq_true h) hc
  · exact h

/-- A shard-local check gives the check against the global table. -/
theorem checkState3cL_sound {top : BT (BT Nat)} {ms : List (Nat × BT Nat)} (hok : ModsOK top ms)
    {N num den i hs : Nat} {d0 d1 d2 : List Nat} (h : checkState3cL ms N num den i hs d0 d1 d2 = true) :
    checkState3c (rdT30 top 64 16384) N num den i hs d0 d1 d2 = true := by
  simp only [checkState3cL, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hi, k0⟩, k1⟩, k2⟩, hc⟩ := h
  have ei : rdKr ms i = rdT30 top 64 16384 i := rdKr_eq hok hi
  rw [ei] at k0 k1 k2
  rw [← checkState3c_congr (rd' := rdKr ms) ei (fun hc0 => rdKr_eq hok (modIn_of_kidIn k0 hc0))
    (fun hc1 => rdKr_eq hok (modIn_of_kidIn k1 hc1)) (fun hc2 => rdKr_eq hok (modIn_of_kidIn k2 hc2))]
  exact hc

/-! ## Ranges -/

def Covered (rd : Nat → Rec) (N num den lo k : Nat) : Prop :=
  ∀ i, lo ≤ i → i < lo + k → ∃ h d0 d1 d2, checkState3c rd N num den i h d0 d1 d2 = true

theorem covered_append {rd : Nat → Rec} {N num den lo a b : Nat} (h1 : Covered rd N num den lo a)
    (h2 : Covered rd N num den (lo + a) b) : Covered rd N num den lo (a + b) := by
  intro i hi1 hi2
  by_cases h : i < lo + a
  · exact h1 i hi1 h
  · exact h2 i (by omega) (by omega)

theorem checkRangeL_covered {top : BT (BT Nat)} {ms : List (Nat × BT Nat)} (hok : ModsOK top ms) {N num den : Nat} :
    ∀ (hs : List (Nat × List Nat × List Nat × List Nat)) (lo : Nat), checkRangeL ms N num den lo hs = true →
    Covered (rdT30 top 64 16384) N num den lo hs.length := by
  intro hs
  induction hs with
  | nil => intro lo _ i h1 h2; simp at h2; omega
  | cons x hs ih =>
    intro lo h i h1 h2
    obtain ⟨hh, d0, d1, d2⟩ := x
    simp only [checkRangeL, Bool.and_eq_true] at h
    by_cases e : i = lo
    · subst e; exact ⟨hh, d0, d1, d2, checkState3cL_sound hok h.1⟩
    · exact ih (lo + 1) h.2 i (by omega) (by simp at h2; omega)

/-- All states covered: the hypothesis of `valid_of_check3c`. -/
theorem hall_of_covered {rd : Nat → Rec} {N num den : Nat} (h : Covered rd N num den 0 N) :
    ∀ i < N, ∃ hh d0 d1 d2, checkState3c rd N num den i hh d0 d1 d2 = true :=
  fun i hi => h i (Nat.zero_le _) (by omega)

end K30BP

end
