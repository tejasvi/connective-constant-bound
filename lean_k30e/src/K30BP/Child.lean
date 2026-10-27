module

public import K30BP.Walk

@[expose] public section

/-!
# Soundness of the hinted child test (speedup study)         

`childOK3c_sound`: if the child record decodes to `C` (known from the child's own check) and the hinted test accepts,
then (C2) holds for the slot: some `g ∈ D₄` maps every cell of `C` (placed at the target) into `E` or onto a dead cell.
The dead-cell part follows `deadTestB2_sound`, with the test chosen by the hint; for test (c) the hinted cut cell is
used directly (the proof of `deadTestB2_sound` never used that its cut cell came from `candsB`).
-/

namespace K30BP

open Saw38aCore Saw38aK Saw38a K30B

theorem tcP_eq {t : Nat} (ht : t < 3) : tcP t = pk (stepC t) := by
  interval_cases t <;> rfl

theorem near_step {T : Saw38a.Cell} (hT : T = (1, 0) ∨ T = (0, 1) ∨ T = (0, -1)) : Near T := by
  rcases hT with rfl | rfl | rfl <;> (unfold Near; decide)

theorem near_tf {g : Nat} (hg : g < 8) {z : Saw38a.Cell} (hz : small z = true) {T : Saw38a.Cell}
    (hT : T = (1, 0) ∨ T = (0, 1) ∨ T = (0, -1)) : Near (tf g T z) := by
  obtain ⟨a, b⟩ := z
  simp only [small, Bool.and_eq_true, decide_eq_true_eq] at hz
  rcases hT with rfl | rfl | rfl <;> interval_cases g <;> simp [tf, addC, d4c, Near] <;> omega

theorem memB_pk {w : Saw38a.Cell} (hw : Near w) (v : Nat) : memB v (offC w).1 (offC w).2 = v.testBit (pk w) := by
  unfold Near at hw
  have h1 : (offC w).1 < 63 := by simp only [offC, ox]; omega
  have h2 : (offC w).2 < 63 := by simp only [offC, ox]; omega
  simp only [memB, h1, h2, decide_true, Bool.true_and]
  rfl

theorem tf_zero_zero (g : Nat) (T : Saw38a.Cell) : tf g T (0, 0) = T := by
  obtain ⟨a, b⟩ := T
  rcases g with _ | _ | _ | _ | _ | _ | _ | _ | g <;> simp [tf, d4c, addC]

theorem tf_first {g : Nat} (hg : g < 8) (T : Saw38a.Cell) :
    tf g T (-1, 0) = (T.1 - (dirI (gdir g 0)).1, T.2 - (dirI (gdir g 0)).2) := by
  have h := tf_step hg (j := 0) (by norm_num) T (0, 0)
  rw [tf_zero_zero] at h
  have e : (((0 : Int), (0 : Int)).1 - (dirI 0).1, ((0 : Int), (0 : Int)).2 - (dirI 0).2) = ((-1 : Int), (0 : Int)) := by
    simp [dirI]
  rw [e] at h
  exact h

theorem decode_some {n T : Nat} {C : List Saw38a.Cell} (h : decode n T = some C) : C = pathOf n T := by
  unfold decode at h
  by_cases h1 : (n < 2 || 40 < n) = true
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : ((digitsQ (n - 2) T).2 != 0) = true
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      dsimp only at h
      by_cases h3 : ((pathOf n T).all small && nodupC (pathOf n T)) = true
      · rw [if_pos h3] at h; exact (Option.some.inj h).symm
      · rw [if_neg h3] at h; cases h

theorem walkIn_eq (Eg : Nat) (sw : Bool) : ∀ k T i p, walkIn Eg sw k T i p = (walkCells sw k T i p).all (bitP Eg) := by
  intro k
  induction k with
  | zero => intro T i p; rfl
  | succ k ih => intro T i p; simp only [walkIn, walkCells, List.all_cons, ih]

theorem walkDeadH_sound (Sg Eg : Nat) (bigb : Box) (tt : Nat × Nat) (sw : Bool) : ∀ k T i p hs,
    walkDeadH Sg Eg bigb tt sw k T i p hs = true →
    ∀ q ∈ walkCells sw k T i p, bitP Eg q = true ∨ ∃ hh, deadH Sg Eg bigb tt q hh = true := by
  intro k
  induction k with
  | zero => intro T i p hs _ q hq; simp [walkCells] at hq
  | succ k ih =>
    intro T i p hs h q hq
    simp only [walkDeadH] at h
    simp only [walkCells, List.mem_cons] at hq
    cases hb : bitP Eg (stepBackP (turnP (swapT sw (Nat.mod T 3)) i) p) with
    | true =>
      rw [hb] at h
      simp only [Bool.cond_true] at h
      rcases hq with rfl | hq
      · exact Or.inl hb
      · exact ih _ _ _ _ h q hq
    | false =>
      rw [hb] at h
      simp only [Bool.cond_false] at h
      cases hs with
      | nil => simp at h
      | cons hh hs' =>
        simp only [Bool.and_eq_true] at h
        rcases hq with rfl | hq
        · exact Or.inr ⟨hh, h.1⟩
        · exact ih _ _ _ _ h.2 q hq

/-- The hinted dead-cell test is sound (as `deadTestB2_sound`). -/
theorem deadH_sound {S : List Saw38a.Cell} (hS : Small S) {t w : Saw38a.Cell} (ht : t = (1, 0) ∨ t = (0, 1) ∨ t = (0, -1))
    (hw1 : 2 ≤ (offC w).1) (hw2 : (offC w).1 ≤ 60) (hw3 : 2 ≤ (offC w).2) (hw4 : (offC w).2 ≤ 60) {bigb : Box} {hh : Nat}
    (h : deadH (gridB (S.map offC)) (setB (gridB (S.map offC)) (offC t).1 (offC t).2) bigb (offC t)
      (64 * (offC w).2 + (offC w).1) hh = true)
    (hw : w ∉ insert t S.toFinset) : Dead S.toFinset t w := by
  refine ⟨hw, ?_⟩
  have hx : Nat.land (64 * (offC w).2 + (offC w).1) 63 = (offC w).1 := by rw [land63]; omega
  have hy : Nat.shiftRight (64 * (offC w).2 + (offC w).1) 6 = (offC w).2 := by rw [shr6]; omega
  have htr : inRange t = true := by rcases ht with rfl | rfl | rfl <;> decide
  have hSg : toGrid (gridB (S.map offC)) = gridOf S := toGrid_gridB S (small_inRange hS)
  have hEg : toGrid (setB (gridB (S.map offC)) (offC t).1 (offC t).2) = add (gridOf S) t := by
    rw [toGrid_setB_add htr, hSg]
  have hrepE : Rep (add (gridOf S) t) (insert t (↑S.toFinset : Set Saw38a.Cell)) :=
    rep_add (gok_gridOf S) (rep_gridOf' S) t
  have hwr : inRange w = true := by
    simp only [offC, ox] at hw1 hw2 hw3 hw4
    simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hwc : cellOf (offC w).1 (offC w).2 = w := cellOf_ox hwr
  obtain ⟨ht1, ht2, ht3, ht4, htc⟩ := offC_step ht
  simp only [deadH, hx, hy, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  by_cases h0 : hh = 0
  · subst h0
    simp only [Nat.beq_refl, Bool.cond_true, Nat.ble_eq] at h
    left
    have ha : 3 ≤ nbCountB (gridB (S.map offC)) ((offC w).1, (offC w).2) := h
    rw [nbCountB_eq (by omega) (by omega) (by omega) (by omega), hSg, hwc] at ha
    rwa [← nbCount_eq hS]
  · have hb0 : Nat.beq hh 0 = false := by
      cases h' : Nat.beq hh 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h') h0
    by_cases h1 : hh = 1
    · subst h1
      simp only [hb0, Bool.cond_false, Nat.beq_refl, Bool.cond_true] at h
      right; left
      rw [← hwc]
      exact not_connInf_of_confinedB (by rw [hEg]; exact blockedIn_of_rep hrepE) h
    · have hb1 : Nat.beq hh 1 = false := by
        cases h' : Nat.beq hh 1
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h') h1
      simp only [hb0, hb1, Bool.cond_false, Bool.and_eq_true] at h
      obtain ⟨-, hC⟩ := h
      right; right
      set wx := Nat.land (hh - 2) 63
      set wy := Nat.shiftRight (hh - 2) 6
      simp only [testCB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hC
      obtain ⟨⟨⟨⟨⟨hwx, hwy⟩, hnE⟩, hne⟩, hconf⟩, htn⟩ := hC
      have hrep2 : Rep (toGrid (setB (setB (gridB (S.map offC)) (offC t).1 (offC t).2) wx wy))
          (insert (cellOf wx wy) (insert t (↑S.toFinset : Set Saw38a.Cell))) := by
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
        obtain ⟨e1, e2⟩ := cellOf_inj heq
        rw [e1, e2] at hne
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

/-- (C2) for a slot from the hinted child test. -/
theorem childOK3c_sound {S C : List Saw38a.Cell} (hS : Small S) {t : Nat} (ht : t < 3) {rc : Rec}
    (hdec : decode rc.n rc.T = some C) {bb : Box} {h : Nat} {dh : List Nat}
    (hok : childOK3c (gridB (S.map offC)) bb t rc h dh = true) :
    ∃ g : Fin 8, ∀ z ∈ C.toFinset, d4 g z + stepC t ∈ insert (stepC t) S.toFinset ∨
      Dead S.toFinset (stepC t) (d4 g z + stepC t) := by
  have hTc := stepC_cases ht
  have hTn := near_step hTc
  have hC : Small C := small_of_decode hdec
  have hCp : C = pathOf rc.n rc.T := decode_some hdec
  have htc : tcP t = pk (stepC t) := tcP_eq ht
  have htr : inRange (stepC t) = true := inRange_stepC ht
  have hSg : toGrid (gridB (S.map offC)) = gridOf S := toGrid_gridB S (small_inRange hS)
  have hEgS : toGrid (setB (gridB (S.map offC)) (offC (stepC t)).1 (offC (stepC t)).2) = add (gridOf S) (stepC t) := by
    rw [toGrid_setB_add htr, hSg]
  have hrepE : Rep (add (gridOf S) (stepC t)) (insert (stepC t) (↑S.toFinset : Set Saw38a.Cell)) :=
    rep_add (gok_gridOf S) (rep_gridOf' S) (stepC t)
  have hEg : Nat.lor (gridB (S.map offC)) (Nat.shiftLeft 1 (tcP t)) =
      setB (gridB (S.map offC)) (offC (stepC t)).1 (offC (stepC t)).2 := by
    rw [htc, shiftLeft_one, pk_offC]; rfl
  simp only [childOK3c, nmod] at hok
  have hg : h % 8 < 8 := Nat.mod_lt _ (by norm_num)
  set g := h % 8 with hgdef
  -- the walk of the child in the frame of `g`
  set gs := genB (dirI 0) (-1, 0) (digitsQ (rc.n - 2) rc.T).1 with hgs
  have hCeq : C = gs.reverse ++ [(-1, 0), (0, 0)] := by rw [hCp, pathOf_eq]
  have hsm : ∀ z ∈ C, small z = true := hC
  have hgsm : ∀ q ∈ gs, small q = true := fun q hq => hsm q (by rw [hCeq]; simp [hq])
  have hp1 : stepBackP (gdir g 0) (tcP t) = pk (tf g (stepC t) (-1, 0)) := by
    rw [htc, tf_first hg]
    refine stepBackP_pk' (gdir_lt g 0) hTn ?_
    rw [← tf_first hg]
    exact near_tf hg (by decide) hTc
  have hwalk : walkCells (Nat.ble 4 g) (rc.n - 2) rc.T (gdir g 0) (stepBackP (gdir g 0) (tcP t)) =
      gs.map (fun q => pk (tf g (stepC t) q)) := by
    rw [hp1]
    exact walkCells_tf hg (stepC t) _ _ 0 (-1, 0) (by norm_num) (near_tf hg (by decide) hTc)
      (fun q hq => near_tf hg (hgsm q hq) hTc)
  -- membership in `E` from a set bit
  have hmem : ∀ z ∈ C, (Nat.lor (gridB (S.map offC)) (Nat.shiftLeft 1 (tcP t))).testBit (pk (tf g (stepC t) z)) = true →
      d4 ⟨g, hg⟩ z + stepC t ∈ insert (stepC t) S.toFinset := by
    intro z hz hb
    have hzs := hsm z hz
    have hwn := near_tf hg hzs hTc
    rw [hEg, ← memB_pk hwn] at hb
    have hm : memO (setB (gridB (S.map offC)) (offC (stepC t)).1 (offC (stepC t)).2) (offC (tf g (stepC t) z)) = true := hb
    unfold tf at hm
    rw [memO_offC (inRange_addC_d4c hg hzs hTc), hEgS] at hm
    have e : addC (d4c g z) (stepC t) = d4 ⟨g, hg⟩ z + stepC t := by rw [addC_eq, ← d4c_eq]
    rw [e] at hm
    have hin : inRange (d4 ⟨g, hg⟩ z + stepC t) = true := by rw [← e]; exact inRange_addC_d4c hg hzs hTc
    have := (hrepE _ hin).1 hm
    simpa [Finset.mem_insert, List.mem_toFinset] using this
  have hlast : (Nat.lor (gridB (S.map offC)) (Nat.shiftLeft 1 (tcP t))).testBit (pk (tf g (stepC t) (0, 0))) = true := by
    rw [tf_zero_zero, ← htc, testBit_lor_shiftLeft]; simp
  refine ⟨⟨g, hg⟩, fun z hz => ?_⟩
  have hz' : z ∈ C := List.mem_toFinset.1 hz
  cases hlt : Nat.blt h 8 with
  | true =>
    rw [hlt] at hok
    simp only [Bool.cond_true, Bool.and_eq_true] at hok
    obtain ⟨h1, h2⟩ := hok
    rw [walkIn_eq, hwalk, List.all_eq_true] at h2
    left
    apply hmem z hz'
    rw [← bitP_eq]
    rw [hCeq] at hz'
    simp only [List.mem_append, List.mem_reverse, List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with hz' | rfl | rfl
    · exact h2 _ (List.mem_map_of_mem hz')
    · rw [← hp1]; exact h1
    · rw [bitP_eq]; exact hlast
  | false =>
    rw [hlt] at hok
    simp only [Bool.cond_false] at hok
    -- every cell: a set bit or a hinted dead test
    have hany : ∀ z ∈ C, bitP (Nat.lor (gridB (S.map offC)) (Nat.shiftLeft 1 (tcP t))) (pk (tf g (stepC t) z)) = true ∨
        ∃ hh, deadH (gridB (S.map offC)) (Nat.lor (gridB (S.map offC)) (Nat.shiftLeft 1 (tcP t)))
          ⟨Nat.min bb.x0 (Nat.land (tcP t) 63) - 3, Nat.max bb.x1 (Nat.land (tcP t) 63) + 3,
            Nat.min bb.y0 (Nat.shiftRight (tcP t) 6) - 3, Nat.max bb.y1 (Nat.shiftRight (tcP t) 6) + 3⟩
          (Nat.land (tcP t) 63, Nat.shiftRight (tcP t) 6) (pk (tf g (stepC t) z)) hh = true := by
      intro z hz
      rw [hCeq] at hz
      simp only [List.mem_append, List.mem_reverse, List.mem_cons, List.not_mem_nil, or_false] at hz
      cases hb1 : bitP (Nat.lor (gridB (S.map offC)) (Nat.shiftLeft 1 (tcP t))) (stepBackP (gdir g 0) (tcP t)) with
      | true =>
        rw [hb1] at hok
        simp only [Bool.cond_true] at hok
        have hw := walkDeadH_sound _ _ _ _ _ _ _ _ _ _ hok
        rw [hwalk] at hw
        rcases hz with hz | rfl | rfl
        · exact hw _ (List.mem_map_of_mem hz)
        · left; rw [← hp1]; exact hb1
        · left; rw [bitP_eq]; exact hlast
      | false =>
        rw [hb1] at hok
        simp only [Bool.cond_false] at hok
        cases dh with
        | nil => simp at hok
        | cons q dh' =>
          simp only [Bool.and_eq_true] at hok
          have hw := walkDeadH_sound _ _ _ _ _ _ _ _ _ _ hok.2
          rw [hwalk] at hw
          rcases hz with hz | rfl | rfl
          · exact hw _ (List.mem_map_of_mem hz)
          · right; rw [← hp1]; exact ⟨q, hok.1⟩
          · left; rw [bitP_eq]; exact hlast
    rcases hany z hz' with hb | ⟨hh, hd⟩
    · left; exact hmem z hz' (by rw [← bitP_eq]; exact hb)
    · by_cases hin : d4 ⟨g, hg⟩ z + stepC t ∈ insert (stepC t) S.toFinset
      · exact Or.inl hin
      · right
        have hzs := hsm z hz'
        have e : tf g (stepC t) z = d4 ⟨g, hg⟩ z + stepC t := by unfold tf; rw [addC_eq, ← d4c_eq]
        have hwn := near_tf hg hzs hTc
        have hx : Nat.land (tcP t) 63 = (offC (stepC t)).1 := by rw [land63, htc, pk_mod hTn]; rfl
        have hy : Nat.shiftRight (tcP t) 6 = (offC (stepC t)).2 := by rw [shr6, htc, pk_div hTn]; rfl
        rw [hx, hy, hEg, pk_offC] at hd
        obtain ⟨r1, r2, r3, r4⟩ := offC_addC_d4c_range hg hzs hTc
        have := deadH_sound hS hTc (w := tf g (stepC t) z) r1 r2 r3 r4 hd (by rw [e]; exact hin)
        rwa [e] at this

end K30BP

end
