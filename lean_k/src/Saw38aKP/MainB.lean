import Saw38aKP.DeadB
import Saw38aKP.DecodeO

/-!
# Soundness of the bitboard checker: the certificate of the data

As `Saw38a/CheckMain.lean`, for `checkStateB2` with records from `rd`: `valid_of_checkB2` shows that the records form
a valid certificate with ratio at most `num / den` when `checkStateB2` accepts every record and record 0 decodes to
the start path. The proofs follow the audited ones; decoding goes through `decodeO_eq`, grids through `toGrid`.
-/

namespace Saw38a

open Saw38aCore Saw38aK

/-! ## Entries (as `entryOK_none`, `entryOK_some`) -/

theorem entryOKB2_none {rd : Nat → Rec} {N : Nat} {S : List Cell} (hS : Small S) {b1 : Box} {t : Nat}
    (ht : t < 3) (h : entryOKB2 rd N (S.map offC) (gridB (S.map offC)) b1 t NONEK = true) :
    stepC t ∈ S ∨ ¬ ConnInf (↑S.toFinset : Set Cell) (stepC t) := by
  have hSg : toGrid (gridB (S.map offC)) = gridOf S := toGrid_gridB S (small_inRange hS)
  simp only [entryOKB2, beq_self_eq_true, ite_true, Bool.or_eq_true] at h
  rw [stepO_eq ht] at h
  rcases h with h | h
  · left
    rw [memO_offC (inRange_stepC ht), hSg] at h
    exact (mem_gridOf_iff hS _).1 h
  · right
    rw [← cellOf_ox (inRange_stepC ht)]
    exact not_connInf_of_confinedB (by rw [hSg]; exact blockedIn_of_rep (rep_gridOf' S)) h

theorem entryOKB2_some {rd : Nat → Rec} {N : Nat} {S : List Cell} (hS : Small S) {b1 : Box} {t c : Nat}
    (ht : t < 3) (hc : c ≠ NONEK) (h : entryOKB2 rd N (S.map offC) (gridB (S.map offC)) b1 t c = true) :
    c < N ∧ (stepC t ∈ S ∨ ∃ C, decode (rd c).n (rd c).T = some C ∧
      childOKB2 (S.map offC) (gridB (S.map offC)) (offC (stepC t)) (C.map offC) = true) := by
  have hSg : toGrid (gridB (S.map offC)) = gridOf S := toGrid_gridB S (small_inRange hS)
  have hb : (c == NONEK) = false := by simpa using hc
  simp only [entryOKB2, hb, Bool.false_eq_true, ite_false, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true] at h
  rw [stepO_eq ht] at h
  obtain ⟨hcN, h⟩ := h
  refine ⟨hcN, ?_⟩
  rcases h with h | h
  · left
    rw [memO_offC (inRange_stepC ht), hSg] at h
    exact (mem_gridOf_iff hS _).1 h
  · right
    revert h
    rw [decodeO_eq]
    cases hd : decode (rd c).n (rd c).T with
    | none => simp
    | some C => intro h; exact ⟨C, rfl, h⟩

/-! ## States (as `checkState_sound`) -/

theorem checkStateB2_sound {rd : Nat → Rec} {N num den i : Nat} (h : checkStateB2 rd N num den i = true) :
    ∃ S, decode (rd i).n (rd i).T = some S ∧ 0 < (rd i).V ∧
      entryOKB2 rd N (S.map offC) (gridB (S.map offC)) (bboxO (S.map offC) 1) 0 (rd i).c0 = true ∧
      entryOKB2 rd N (S.map offC) (gridB (S.map offC)) (bboxO (S.map offC) 1) 1 (rd i).c1 = true ∧
      entryOKB2 rd N (S.map offC) (gridB (S.map offC)) (bboxO (S.map offC) 1) 2 (rd i).c2 = true ∧
      den * (childVK rd (rd i).c0 + childVK rd (rd i).c1 + childVK rd (rd i).c2) ≤ num * (rd i).V := by
  unfold checkStateB2 at h
  dsimp only at h
  rw [decodeO_eq] at h
  cases hd : decode (rd i).n (rd i).T with
  | none => rw [hd] at h; simp at h
  | some S =>
    rw [hd] at h
    simp only [Option.map_some, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hV, h0⟩, h1⟩, h2⟩, hr⟩ := h
    exact ⟨S, rfl, hV, h0, h1, h2, hr⟩

/-! ## The certificate of the data (as `certOf`, `valid_of_check`) -/

/-- The certificate whose states are the records `rd 0, …, rd (N - 1)`; record 0 is the start state. -/
def certOfB (rd : Nat → Rec) (N : Nat) (hN : 0 < N) : Cert where
  N := N
  path i := (decode (rd i).n (rd i).T).getD []
  V i := (rd i).V
  entry i t := if slotC (rd i) t = NONEK then none
    else if h : slotC (rd i) t < N then some ⟨_, h⟩ else none
  start := ⟨0, hN⟩

/-- The checks of all records give a valid certificate of ratio at most `num / den`. -/
theorem valid_of_checkB2 {rd : Nat → Rec} {N num den K : Nat} (hN : 0 < N)
    (hall : ∀ i < N, checkStateB2 rd N num den i = true)
    (hstart : decode (rd 0).n (rd 0).T = some (startPath K)) :
    (certOfB rd N hN).Valid K ∧ (certOfB rd N hN).RatioLE num den := by
  have hloc : ∀ i : Fin N, ∃ S, decode (rd i).n (rd i).T = some S ∧ (certOfB rd N hN).path i = S := by
    intro i
    obtain ⟨S, hd, -⟩ := checkStateB2_sound (hall i i.2)
    exact ⟨S, hd, by simp [certOfB, hd]⟩
  have slot_spec : ∀ (i : Fin N) (t : Fin 3) (S : List Cell),
      decode (rd i).n (rd i).T = some S →
      entryOKB2 rd N (S.map offC) (gridB (S.map offC)) (bboxO (S.map offC) 1) t.val (slotC (rd i) t) = true := by
    intro i t S hd
    obtain ⟨S', hd', -, h0, h1, h2, -⟩ := checkStateB2_sound (hall i i.2)
    rw [hd] at hd'; cases hd'
    fin_cases t
    · simpa [slotC] using h0
    · simpa [slotC] using h1
    · simpa [slotC] using h2
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    obtain ⟨S, hd, hp⟩ := hloc i
    rw [hp]; exact decode_isState hd
  · simp [certOfB, hstart]
  · intro i
    obtain ⟨S, -, hV, -⟩ := checkStateB2_sound (hall i i.2)
    exact hV
  · intro i t ht
    obtain ⟨S, hd, hp⟩ := hloc i
    have hS := small_of_decode hd
    have hslot := slot_spec i t S hd
    have hnone : slotC (rd i) t = NONEK := by
      by_contra hne
      have := (entryOKB2_some hS t.2 hne hslot).1
      simp [certOfB, hne, this] at ht
    rw [hnone] at hslot
    have := entryOKB2_none hS t.2 hslot
    simp only [Cert.cells, hp, List.mem_toFinset, ← stepC_fin t]
    exact this
  · intro i t j hj ht
    obtain ⟨S, hd, hp⟩ := hloc i
    have hS := small_of_decode hd
    have hslot := slot_spec i t S hd
    have hne : slotC (rd i) t ≠ NONEK := by
      intro h; simp [certOfB, h] at hj
    obtain ⟨hcN, hor⟩ := entryOKB2_some hS t.2 hne hslot
    have hjv : j.val = slotC (rd i) t := by
      simp only [certOfB, hne, ite_false, hcN, dite_true] at hj
      have := Option.some.inj hj
      rw [← this]
    simp only [Cert.cells, hp, List.mem_toFinset, ← stepC_fin t] at ht ⊢
    rcases hor with hin | ⟨C, hdC, hok⟩
    · exact absurd hin ht
    · have hpj : (certOfB rd N hN).path j = C := by
        simp only [certOfB, hjv, hdC, Option.getD_some]
      rw [hpj]
      have hst : stepC t.val = (1, 0) ∨ stepC t.val = (0, 1) ∨ stepC t.val = (0, -1) := stepC_cases t.2
      obtain ⟨g, hg⟩ := childOKB2_sound hS (small_of_decode hdC) hst hok
      exact ⟨g, fun z hz => by simpa [List.mem_toFinset] using hg z (List.mem_toFinset.2 hz)⟩
  · intro i
    obtain ⟨S, hd, -, h0, h1, h2, hr⟩ := checkStateB2_sound (hall i i.2)
    have hS := small_of_decode hd
    have hsum : (certOfB rd N hN).childSum i = ∑ t : Fin 3, childVK rd (slotC (rd i) t) := by
      unfold Cert.childSum
      refine Finset.sum_congr rfl (fun t _ => ?_)
      have hslot := slot_spec i t S hd
      by_cases hc : slotC (rd i) t = NONEK
      · have hE : (certOfB rd N hN).entry i t = none := by simp [certOfB, hc]
        rw [hE]; simp [childVK, hc]
      · have hcN := (entryOKB2_some hS t.2 hc hslot).1
        have hE : (certOfB rd N hN).entry i t = some ⟨_, hcN⟩ := by simp [certOfB, hc, hcN]
        rw [hE]
        have hb : (slotC (rd i) t == NONEK) = false := by simpa using hc
        simp [childVK, hb, certOfB]
    show den * (certOfB rd N hN).childSum i ≤ num * (certOfB rd N hN).V i
    rw [hsum, Fin.sum_univ_three]
    simpa [slotC, certOfB] using hr

/-! ## Ranges -/

theorem checkRangeB2_sound {rd : Nat → Rec} {N num den lo k : Nat} (h : checkRangeB2 rd N num den lo k = true) :
    ∀ i, lo ≤ i → i < lo + k → checkStateB2 rd N num den i = true :=
  fun i h1 h2 => allFrom_true h i h1 h2

/-- Two adjacent ranges. -/
theorem checkRangeB2_append {rd : Nat → Rec} {N num den lo a b : Nat} (h1 : checkRangeB2 rd N num den lo a = true)
    (h2 : checkRangeB2 rd N num den (lo + a) b = true) : checkRangeB2 rd N num den lo (a + b) = true := by
  apply allFrom_of_forall
  intro i hi1 hi2
  by_cases h : i < lo + a
  · exact checkRangeB2_sound h1 i hi1 h
  · exact checkRangeB2_sound h2 i (by omega) (by omega)

end Saw38a
