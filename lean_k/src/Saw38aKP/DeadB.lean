import Saw38aKP.Close

/-!
# Dead cells and children on bitboards

`deadTestB2` implies `Dead` and `childOKB2` implies (C2), as `deadTest_sound` and `childOK_sound` of the audited
`Saw38a/CheckDead.lean`; the proofs follow those, with the bitboards read through `toGrid`.
-/

namespace Saw38a

open Saw38aCore Saw38aK

/-! ## Neighbours in offset coordinates -/

theorem addC_cellOf_dir {x y : Nat} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    addC (cellOf x y) (dirC 0) = cellOf (x + 1) y ∧ addC (cellOf x y) (dirC 1) = cellOf (x - 1) y ∧
    addC (cellOf x y) (dirC 2) = cellOf x (y + 1) ∧ addC (cellOf x y) (dirC 3) = cellOf x (y - 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> refine Prod.ext ?_ ?_ <;> simp [addC, dirC, cellOf] <;> omega

theorem mem_toGrid_cellOf {g x y : Nat} (hx : x < 63) (hy : y < 63) : mem (toGrid g) (cellOf x y) = memB g x y := by
  rw [mem_cellOf _ hx hy, memN_toGrid]

theorem nbCountB_eq {g x y : Nat} (hx1 : 1 ≤ x) (hx2 : x ≤ 61) (hy1 : 1 ≤ y) (hy2 : y ≤ 61) :
    nbCountB g (x, y) = nbCount (toGrid g) (cellOf x y) := by
  obtain ⟨e0, e1, e2, e3⟩ := addC_cellOf_dir (x := x) (y := y) hx1 hy1
  simp only [nbCountB, nbCount, e0, e1, e2, e3, mem_toGrid_cellOf (show x + 1 < 63 by omega) (show y < 63 by omega),
    mem_toGrid_cellOf (show x - 1 < 63 by omega) (show y < 63 by omega),
    mem_toGrid_cellOf (show x < 63 by omega) (show y + 1 < 63 by omega),
    mem_toGrid_cellOf (show x < 63 by omega) (show y - 1 < 63 by omega)]

theorem tNbrsOKB_eq {blk R x y : Nat} (hx1 : 1 ≤ x) (hx2 : x ≤ 61) (hy1 : 1 ≤ y) (hy2 : y ≤ 61) :
    tNbrsOKB blk R (x, y) = tNbrsOK (toGrid blk) (toGrid R) (cellOf x y) := by
  obtain ⟨e0, e1, e2, e3⟩ := addC_cellOf_dir (x := x) (y := y) hx1 hy1
  simp only [tNbrsOKB, tNbrsOK, e0, e1, e2, e3,
    mem_toGrid_cellOf (g := blk) (show x + 1 < 63 by omega) (show y < 63 by omega),
    mem_toGrid_cellOf (g := blk) (show x - 1 < 63 by omega) (show y < 63 by omega),
    mem_toGrid_cellOf (g := blk) (show x < 63 by omega) (show y + 1 < 63 by omega),
    mem_toGrid_cellOf (g := blk) (show x < 63 by omega) (show y - 1 < 63 by omega),
    mem_toGrid_cellOf (g := R) (show x + 1 < 63 by omega) (show y < 63 by omega),
    mem_toGrid_cellOf (g := R) (show x - 1 < 63 by omega) (show y < 63 by omega),
    mem_toGrid_cellOf (g := R) (show x < 63 by omega) (show y + 1 < 63 by omega),
    mem_toGrid_cellOf (g := R) (show x < 63 by omega) (show y - 1 < 63 by omega)]

theorem offC_step {t : Cell} (ht : t = (1, 0) ∨ t = (0, 1) ∨ t = (0, -1)) :
    1 ≤ (offC t).1 ∧ (offC t).1 ≤ 61 ∧ 1 ≤ (offC t).2 ∧ (offC t).2 ≤ 61 ∧ cellOf (offC t).1 (offC t).2 = t := by
  rcases ht with rfl | rfl | rfl <;> decide

/-! ## Dead cells (as `no_reach_tNbr` and `deadTest_sound`) -/

theorem no_reach_tNbrB {blk R : Nat} {b : Box} {X : Set Cell} (hrep : Rep (toGrid blk) X) {x y : Nat} {t : Cell}
    (ht : t = (1, 0) ∨ t = (0, 1) ∨ t = (0, -1)) (hc : confinedB blk R b x y = true)
    (hn : tNbrsOK (toGrid blk) (toGrid R) t = true) :
    ∀ u, Adj u t → u ∉ X → ¬ Reach X (cellOf x y) u := by
  intro u hu huX hr
  have hin := reach_of_confinedB (blockedIn_of_rep hrep) hc u hr
  obtain ⟨x', y', rfl, -, hx1, -, hy1, hm⟩ := hin
  obtain ⟨hbx, hby, -, -⟩ := confinedB_parts hc
  have hmem : mem (toGrid R) (cellOf x' y') = true := by rw [mem_cellOf _ (by omega) (by omega)]; exact hm
  have hnot : ∀ k : Fin 4, cellOf x' y' = t + dir k → False := by
    intro k hk
    have hinr := small_of_inRange_step ht k
    rw [← hk] at hinr
    have hb : mem (toGrid blk) (cellOf x' y') = false := by
      cases h : mem (toGrid blk) (cellOf x' y')
      · rfl
      · exact absurd ((hrep _ hinr).1 h) huX
    simp only [tNbrsOK, addC_eq, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hn
    have e : ∀ k : Fin 4, dirC k = dir k := dirC_eq
    rw [show dirC 0 = dir 0 from e 0, show dirC 1 = dir 1 from e 1, show dirC 2 = dir 2 from e 2,
      show dirC 3 = dir 3 from e 3] at hn
    fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hk <;> rw [← hk] at hn <;>
      simp_all
  rcases adj_cases hu with h | h | h | h
  · exact hnot 0 h
  · exact hnot 1 h
  · exact hnot 2 h
  · exact hnot 3 h

theorem deadTestB2_sound {S : List Cell} (hS : Small S) {t w : Cell} (ht : t = (1, 0) ∨ t = (0, 1) ∨ t = (0, -1))
    (hw1 : 2 ≤ (offC w).1) (hw2 : (offC w).1 ≤ 60) (hw3 : 2 ≤ (offC w).2) (hw4 : (offC w).2 ≤ 60) {bigb : Box}
    (h : deadTestB2 (gridB (S.map offC)) (setB (gridB (S.map offC)) (offC t).1 (offC t).2) bigb (offC t) (offC w) = true)
    (hw : w ∉ insert t S.toFinset) : Dead S.toFinset t w := by
  refine ⟨hw, ?_⟩
  have htr : inRange t = true := by rcases ht with rfl | rfl | rfl <;> decide
  have hSg : toGrid (gridB (S.map offC)) = gridOf S := toGrid_gridB S (small_inRange hS)
  have hEg : toGrid (setB (gridB (S.map offC)) (offC t).1 (offC t).2) = add (gridOf S) t := by
    rw [toGrid_setB_add htr, hSg]
  have hrepE : Rep (add (gridOf S) t) (insert t (↑S.toFinset : Set Cell)) :=
    rep_add (gok_gridOf S) (rep_gridOf' S) t
  have hwr : inRange w = true := by
    simp only [offC, ox] at hw1 hw2 hw3 hw4
    simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hwc : cellOf (offC w).1 (offC w).2 = w := cellOf_ox hwr
  obtain ⟨ht1, ht2, ht3, ht4, htc⟩ := offC_step ht
  simp only [deadTestB2, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h⟩ := h
  rcases h with ha | hb | hc
  · left
    rw [show offC w = ((offC w).1, (offC w).2) from rfl, nbCountB_eq (by omega) (by omega) (by omega) (by omega), hSg,
      hwc] at ha
    rwa [← nbCount_eq hS]
  · right; left
    rw [← hwc]
    exact not_connInf_of_confinedB (by rw [hEg]; exact blockedIn_of_rep hrepE) hb
  · right; right
    obtain ⟨-, hany⟩ := hc
    obtain ⟨⟨wx, wy⟩, -, hC⟩ := Array.any_eq_true'.1 hany
    simp only [testCB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at hC
    obtain ⟨⟨⟨⟨⟨hwx, hwy⟩, hnE⟩, hne⟩, hconf⟩, htn⟩ := hC
    have hrep2 : Rep (toGrid (setB (setB (gridB (S.map offC)) (offC t).1 (offC t).2) wx wy))
        (insert (cellOf wx wy) (insert t (↑S.toFinset : Set Cell))) := by
      rw [toGrid_setB (by omega) (by omega), hEg, ← add_cellOf _ hwx hwy]
      exact rep_add (gok_add (gok_gridOf S) t) hrepE _
    refine ⟨cellOf wx wy, ?_, ?_, ?_, ?_⟩
    · intro hmem
      have hin : inRange (cellOf wx wy) = true := by simp [inRange, cellOf]; omega
      have := (hrepE _ hin).2 (by simpa [Finset.mem_insert, List.mem_toFinset] using hmem)
      rw [← hEg, mem_toGrid_cellOf (by omega) (by omega)] at this
      simp [this] at hnE
    · intro heq
      rw [← hwc] at heq
      obtain ⟨h1, h2⟩ := cellOf_inj heq
      subst h1; subst h2
      simp at hne
    · rw [← hwc]; exact not_connInf_of_confinedB (blockedIn_of_rep hrep2) hconf
    · intro u hu huX
      rw [← hwc]
      refine no_reach_tNbrB hrep2 ht hconf ?_ u hu huX
      have e := tNbrsOKB_eq (blk := setB (setB (gridB (S.map offC)) (offC t).1 (offC t).2) wx wy)
        (R := floodB (setB (setB (gridB (S.map offC)) (offC t).1 (offC t).2) wx wy) bigb (offC w).1 (offC w).2)
        ht1 ht2 ht3 ht4
      rw [htc] at e
      rw [← e]
      exact htn

/-! ## Children (as `childOK_sound`) -/

theorem childOKB2_sound {S C : List Cell} (hS : Small S) (hC : Small C) {t : Cell}
    (ht : t = (1, 0) ∨ t = (0, 1) ∨ t = (0, -1))
    (h : childOKB2 (S.map offC) (gridB (S.map offC)) (offC t) (C.map offC) = true) :
    ∃ g : Fin 8, ∀ z ∈ C.toFinset, d4 g z + t ∈ insert t S.toFinset ∨ Dead S.toFinset t (d4 g z + t) := by
  have htr : inRange t = true := by rcases ht with rfl | rfl | rfl <;> decide
  have hSg : toGrid (gridB (S.map offC)) = gridOf S := toGrid_gridB S (small_inRange hS)
  have hEg : toGrid (setB (gridB (S.map offC)) (offC t).1 (offC t).2) = add (gridOf S) t := by
    rw [toGrid_setB_add htr, hSg]
  have hrepE : Rep (add (gridOf S) t) (insert t (↑S.toFinset : Set Cell)) :=
    rep_add (gok_gridOf S) (rep_gridOf' S) t
  -- membership of `g z + t` in `E`, read from the bitboard
  have hmemE : ∀ (g : Nat) (hg : g < 8) (z : Cell), z ∈ C →
      memO (setB (gridB (S.map offC)) (offC t).1 (offC t).2) (addO (d4o g (offC z)) (offC t)) = true →
      d4 ⟨g, hg⟩ z + t ∈ insert t S.toFinset := by
    intro g hg z hz hm
    have hzs := hC z hz
    rw [offC_addC_d4c hg hzs ht, memO_offC (inRange_addC_d4c hg hzs ht), hEg] at hm
    have e : addC (d4c g z) t = d4 ⟨g, hg⟩ z + t := by rw [addC_eq, ← d4c_eq]
    rw [e] at hm
    have hin : inRange (d4 ⟨g, hg⟩ z + t) = true := by rw [← e]; exact inRange_addC_d4c hg hzs ht
    have := (hrepE _ hin).1 hm
    simpa [Finset.mem_insert, List.mem_toFinset] using this
  simp only [childOKB2, List.any_eq_true, List.mem_range, List.all_eq_true, Bool.or_eq_true, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h
  rcases h with ⟨g, hg, hq⟩ | ⟨g, hg, hall⟩
  · exact ⟨⟨g, hg⟩, fun z hz => Or.inl (hmemE g hg z (List.mem_toFinset.1 hz) (hq z (List.mem_toFinset.1 hz)))⟩
  refine ⟨⟨g, hg⟩, fun z hz => ?_⟩
  have hz' : z ∈ C := List.mem_toFinset.1 hz
  have hzs := hC z hz'
  rcases hall z hz' with hm | hd
  · exact Or.inl (hmemE g hg z hz' hm)
  · by_cases hmem : d4 ⟨g, hg⟩ z + t ∈ insert t S.toFinset
    · exact Or.inl hmem
    · right
      have e : addC (d4c g z) t = d4 ⟨g, hg⟩ z + t := by rw [addC_eq, ← d4c_eq]
      obtain ⟨r1, r2, r3, r4⟩ := offC_addC_d4c_range hg hzs ht
      rw [offC_addC_d4c hg hzs ht] at hd
      have := deadTestB2_sound hS ht r1 r2 r3 r4 hd (by rw [e]; exact hmem)
      rwa [e] at this

end Saw38a
