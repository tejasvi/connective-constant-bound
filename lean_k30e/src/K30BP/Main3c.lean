module

public import K30BP.Child

@[expose] public section

/-!
# Soundness of `checkState3c` (speedup study): the certificate of the data         

As `Saw38aKP/MainB.lean`, for `checkState3c`, with the `∅` index `NONE30` and the start state at any index `s`.
The one structural change: a parent's slot test does not re-validate the child's decode (it walks the child's cells
without checks); `valid_of_check3c` takes the checks of all states (`hall`) and reads the child's decode from the
child's own check.
-/

namespace K30BP

open Saw38aCore Saw38aK Saw38a K30B

/-! ## Entries -/

theorem entry3c_none {rd : Nat → Rec} {N : Nat} {S : List Saw38a.Cell} (hS : Small S) {bb b1 : Box} {t h : Nat}
    {dh : List Nat} (ht : t < 3) (hok : entryOK3c rd N (gridB (S.map offC)) bb b1 t NONE30 h dh = true) :
    stepC t ∈ S ∨ ¬ ConnInf (↑S.toFinset : Set Saw38a.Cell) (stepC t) := by
  have hSg : toGrid (gridB (S.map offC)) = gridOf S := toGrid_gridB S (small_inRange hS)
  have htc : tcP t = pk (stepC t) := tcP_eq ht
  have hTn := near_step (stepC_cases ht)
  have hx : Nat.land (tcP t) 63 = (offC (stepC t)).1 := by rw [land63, htc, pk_mod hTn]; rfl
  have hy : Nat.shiftRight (tcP t) 6 = (offC (stepC t)).2 := by rw [shr6, htc, pk_div hTn]; rfl
  simp only [entryOK3c, Nat.beq_refl, Bool.cond_true, Bool.or_eq_true, hx, hy] at hok
  rcases hok with h1 | h2
  · left
    rw [htc, bitP_eq, ← memB_pk hTn] at h1
    have h1' : memO (gridB (S.map offC)) (offC (stepC t)) = true := h1
    rw [memO_offC (inRange_stepC ht), hSg] at h1'
    exact (mem_gridOf_iff hS _).1 h1'
  · right
    rw [← cellOf_ox (inRange_stepC ht)]
    exact not_connInf_of_confinedB (by rw [hSg]; exact blockedIn_of_rep (rep_gridOf' S)) h2

theorem entry3c_some {rd : Nat → Rec} {N : Nat} {S : List Saw38a.Cell} (hS : Small S) {bb b1 : Box} {t c h : Nat}
    {dh : List Nat} (ht : t < 3) (hc : c ≠ NONE30) (hok : entryOK3c rd N (gridB (S.map offC)) bb b1 t c h dh = true) :
    c < N ∧ (stepC t ∈ S ∨ childOK3c (gridB (S.map offC)) bb t (rd c) h dh = true) := by
  have hSg : toGrid (gridB (S.map offC)) = gridOf S := toGrid_gridB S (small_inRange hS)
  have htc : tcP t = pk (stepC t) := tcP_eq ht
  have hTn := near_step (stepC_cases ht)
  have hb : Nat.beq c NONE30 = false := by
    cases h' : Nat.beq c NONE30
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true h') hc
  simp only [entryOK3c, hb, Bool.cond_false, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at hok
  obtain ⟨hcN, hor⟩ := hok
  refine ⟨hcN, ?_⟩
  rcases hor with h1 | h2
  · left
    rw [htc, bitP_eq, ← memB_pk hTn] at h1
    have h1' : memO (gridB (S.map offC)) (offC (stepC t)) = true := h1
    rw [memO_offC (inRange_stepC ht), hSg] at h1'
    exact (mem_gridOf_iff hS _).1 h1'
  · right; exact h2

/-! ## States -/

theorem checkState3c_sound {rd : Nat → Rec} {N num den i hs : Nat} {d0 d1 d2 : List Nat}
    (h : checkState3c rd N num den i hs d0 d1 d2 = true) :
    ∃ S, decode (rd i).n (rd i).T = some S ∧ 0 < (rd i).V ∧ ∃ bb b1 : Box,
      (∃ h0, entryOK3c rd N (gridB (S.map offC)) bb b1 0 (rd i).c0 h0 d0 = true) ∧
      (∃ h1, entryOK3c rd N (gridB (S.map offC)) bb b1 1 (rd i).c1 h1 d1 = true) ∧
      (∃ h2, entryOK3c rd N (gridB (S.map offC)) bb b1 2 (rd i).c2 h2 d2 = true) ∧
      den * (childV30 rd (rd i).c0 + childV30 rd (rd i).c1 + childV30 rd (rd i).c2) ≤ num * (rd i).V := by
  unfold checkState3c at h
  dsimp only at h
  cases hd : ownDec (rd i).n (rd i).T with
  | none => rw [hd] at h; simp at h
  | some x =>
    obtain ⟨Sg, bb⟩ := x
    rw [hd] at h
    dsimp only at h
    obtain ⟨S, hS, hSg⟩ := ownDec_sound hd
    subst hSg
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
    obtain ⟨⟨⟨⟨hV, e0⟩, e1⟩, e2⟩, hr⟩ := h
    exact ⟨S, hS, hV, bb, _, ⟨_, e0⟩, ⟨_, e1⟩, ⟨_, e2⟩, hr⟩

/-! ## The certificate of the data -/

/-- The certificate whose states are the records `rd 0, …, rd (N - 1)`, with start state `s`. -/
def certOf30 (rd : Nat → Rec) (N s : Nat) (hs : s < N) : Cert where
  N := N
  path i := (decode (rd i).n (rd i).T).getD []
  V i := (rd i).V
  entry i t := if slotC (rd i) t = NONE30 then none
    else if h : slotC (rd i) t < N then some ⟨_, h⟩ else none
  start := ⟨s, hs⟩

/-- The checks of all records give a valid certificate of ratio at most `num / den`. -/
theorem valid_of_check3c {rd : Nat → Rec} {N num den K s : Nat} (hs : s < N)
    (hall : ∀ i < N, ∃ h d0 d1 d2, checkState3c rd N num den i h d0 d1 d2 = true)
    (hstart : decode (rd s).n (rd s).T = some (startPath K)) :
    (certOf30 rd N s hs).Valid K ∧ (certOf30 rd N s hs).RatioLE num den := by
  have hsound : ∀ i < N, ∃ S, decode (rd i).n (rd i).T = some S ∧ 0 < (rd i).V ∧ ∃ bb b1 : Box,
      (∃ h0 d0, entryOK3c rd N (gridB (S.map offC)) bb b1 0 (rd i).c0 h0 d0 = true) ∧
      (∃ h1 d1, entryOK3c rd N (gridB (S.map offC)) bb b1 1 (rd i).c1 h1 d1 = true) ∧
      (∃ h2 d2, entryOK3c rd N (gridB (S.map offC)) bb b1 2 (rd i).c2 h2 d2 = true) ∧
      den * (childV30 rd (rd i).c0 + childV30 rd (rd i).c1 + childV30 rd (rd i).c2) ≤ num * (rd i).V := by
    intro i hi
    obtain ⟨h, d0, d1, d2, hc⟩ := hall i hi
    obtain ⟨S, hd, hV, bb, b1, ⟨h0, e0⟩, ⟨h1, e1⟩, ⟨h2, e2⟩, hr⟩ := checkState3c_sound hc
    exact ⟨S, hd, hV, bb, b1, ⟨h0, d0, e0⟩, ⟨h1, d1, e1⟩, ⟨h2, d2, e2⟩, hr⟩
  have hloc : ∀ i : Fin N, ∃ S, decode (rd i).n (rd i).T = some S ∧ (certOf30 rd N s hs).path i = S := by
    intro i
    obtain ⟨S, hd, -⟩ := hsound i i.2
    exact ⟨S, hd, by simp [certOf30, hd]⟩
  have slot_spec : ∀ (i : Fin N) (t : Fin 3) (S : List Saw38a.Cell), decode (rd i).n (rd i).T = some S →
      ∃ bb b1 h dh, entryOK3c rd N (gridB (S.map offC)) bb b1 t.val (slotC (rd i) t) h dh = true := by
    intro i t S hd
    obtain ⟨S', hd', -, bb, b1, ⟨h0, d0, e0⟩, ⟨h1, d1, e1⟩, ⟨h2, d2, e2⟩, -⟩ := hsound i i.2
    rw [hd] at hd'; cases hd'
    fin_cases t
    · exact ⟨bb, b1, h0, d0, by simpa [slotC] using e0⟩
    · exact ⟨bb, b1, h1, d1, by simpa [slotC] using e1⟩
    · exact ⟨bb, b1, h2, d2, by simpa [slotC] using e2⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    obtain ⟨S, hd, hp⟩ := hloc i
    rw [hp]; exact decode_isState hd
  · simp [certOf30, hstart]
  · intro i
    obtain ⟨S, -, hV, -⟩ := hsound i i.2
    exact hV
  · intro i t ht
    obtain ⟨S, hd, hp⟩ := hloc i
    have hS := small_of_decode hd
    obtain ⟨bb, b1, h, dh, hslot⟩ := slot_spec i t S hd
    have hnone : slotC (rd i) t = NONE30 := by
      by_contra hne
      have := (entry3c_some hS t.2 hne hslot).1
      simp [certOf30, hne, this] at ht
    rw [hnone] at hslot
    have := entry3c_none hS t.2 hslot
    simp only [Cert.cells, hp, List.mem_toFinset, ← stepC_fin t]
    exact this
  · intro i t j hj ht
    obtain ⟨S, hd, hp⟩ := hloc i
    have hS := small_of_decode hd
    obtain ⟨bb, b1, h, dh, hslot⟩ := slot_spec i t S hd
    have hne : slotC (rd i) t ≠ NONE30 := by
      intro h'; simp [certOf30, h'] at hj
    obtain ⟨hcN, hor⟩ := entry3c_some hS t.2 hne hslot
    have hjv : j.val = slotC (rd i) t := by
      simp only [certOf30, hne, ite_false, hcN, dite_true] at hj
      have := Option.some.inj hj
      rw [← this]
    simp only [Cert.cells, hp, List.mem_toFinset, ← stepC_fin t] at ht ⊢
    rcases hor with hin | hok
    · exact absurd hin ht
    · obtain ⟨C, hdC, -⟩ := hsound _ hcN
      have hpj : (certOf30 rd N s hs).path j = C := by
        simp only [certOf30, hjv, hdC, Option.getD_some]
      rw [hpj]
      obtain ⟨g, hg⟩ := childOK3c_sound hS t.2 hdC hok
      exact ⟨g, fun z hz => by simpa [List.mem_toFinset] using hg z (List.mem_toFinset.2 hz)⟩
  · intro i
    obtain ⟨S, hd, -, -, -, -, -, -, hr⟩ := hsound i i.2
    have hS := small_of_decode hd
    have hsum : (certOf30 rd N s hs).childSum i = ∑ t : Fin 3, childV30 rd (slotC (rd i) t) := by
      unfold Cert.childSum
      refine Finset.sum_congr rfl (fun t _ => ?_)
      obtain ⟨bb', b1', h', dh', hslot⟩ := slot_spec i t S hd
      by_cases hc : slotC (rd i) t = NONE30
      · have hE : (certOf30 rd N s hs).entry i t = none := by simp [certOf30, hc]
        rw [hE]; simp [childV30, hc]
      · have hcN := (entry3c_some hS t.2 hc hslot).1
        have hE : (certOf30 rd N s hs).entry i t = some ⟨_, hcN⟩ := by simp [certOf30, hc, hcN]
        rw [hE]
        have hb : (slotC (rd i) t == NONE30) = false := by simpa using hc
        simp [childV30, hb, certOf30]
    show den * (certOf30 rd N s hs).childSum i ≤ num * (certOf30 rd N s hs).V i
    rw [hsum, Fin.sum_univ_three]
    simpa [slotC, certOf30] using hr

end K30BP

end
