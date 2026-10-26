import Saw38aKP.Grid

/-!
# The bit-parallel closure test implies the audited one

`closedB blk R b` (whole-bitboard operations) implies `closedIn (toGrid blk) (toGrid R) b` for boxes inside
`[0, 62]²`. Hence `confinedB` gives the conclusions of the audited `confined`.
-/

namespace Saw38a

open Saw38aCore Saw38aK

/-! ## Masks -/

theorem testBit_maskC (x0 x1 i : Nat) :
    (maskC x0 x1).testBit i = (decide (x0 ≤ i) && decide (i ≤ x1) && decide (i ≤ 62)) := by
  unfold maskC
  split_ifs with h
  · rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases h1 : x0 ≤ i
    · have e : decide (i - x0 < min x1 62 + 1 - x0) = (decide (i ≤ x1) && decide (i ≤ 62)) := by
        by_cases h2 : i ≤ x1 <;> by_cases h3 : i ≤ 62 <;> simp only [h2, h3, decide_true, decide_false,
          Bool.and_true, Bool.and_false, Bool.false_and, decide_eq_true_eq, decide_eq_false_iff_not] <;> omega
      simp only [ge_iff_le, h1, decide_true, Bool.true_and, e]
    · simp [h1]
  · simp only [Nat.zero_testBit]
    by_cases h1 : x0 ≤ i <;> by_cases h2 : i ≤ x1 <;> by_cases h3 : i ≤ 62 <;>
      simp only [h1, h2, h3, decide_true, decide_false, Bool.and_true, Bool.and_false, Bool.false_and,
        Bool.true_and] <;> omega

theorem maskC_lt (x0 x1 : Nat) : maskC x0 x1 < 2 ^ 64 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_maskC]
  simp
  omega

theorem testBit_maskRows {m : Nat} (hm : m < 2 ^ 64) (k : Nat) : ∀ (r x y : Nat), x < 64 →
    (maskRows m r k).testBit (64 * y + x) = (decide (r ≤ y) && decide (y < r + k) && m.testBit x) := by
  induction k with
  | zero =>
    intro r x y hx
    simp only [maskRows, Nat.zero_testBit]
    by_cases h : r ≤ y <;> simp [h] <;> omega
  | succ k ih =>
    intro r x y hx
    simp only [maskRows, Nat.testBit_or, Nat.testBit_shiftLeft, ih (r + 1) x y hx]
    by_cases hry : r = y
    · subst hry
      have : 64 * r + x - 64 * r = x := by omega
      simp [this]
    · by_cases hlt : y < r
      · have h1 : ¬ (64 * y + x ≥ 64 * r) := by omega
        have h2 : ¬ (r + 1 ≤ y) := by omega
        have h3 : ¬ (r ≤ y) := by omega
        simp [h1, h2, h3]
      · have hge : 64 * y + x ≥ 64 * r := by omega
        have hbig : m.testBit (64 * y + x - 64 * r) = false := by
          apply Nat.testBit_eq_false_of_lt
          calc m < 2 ^ 64 := hm
            _ ≤ 2 ^ (64 * y + x - 64 * r) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : r + 1 ≤ y := by omega
        have h3 : r ≤ y := by omega
        simp only [hge, hbig, h2, h3, decide_true, Bool.true_and, Bool.false_or]
        congr 1
        simp only [decide_eq_decide]
        omega

theorem testBit_boxMaskB (b : Box) (x y : Nat) (hx : x < 64) :
    (boxMaskB b).testBit (64 * y + x) =
      (decide (b.y0 ≤ y) && decide (y ≤ b.y1) && decide (y ≤ 62) &&
        (decide (b.x0 ≤ x) && decide (x ≤ b.x1) && decide (x ≤ 62))) := by
  unfold boxMaskB
  rw [testBit_maskRows (maskC_lt _ _) _ _ _ _ hx, testBit_maskC]
  congr 1
  by_cases h1 : b.y0 ≤ y <;> by_cases h2 : y ≤ b.y1 <;> by_cases h3 : y ≤ 62 <;> simp [h1, h2, h3] <;> omega

theorem testBit_innerMaskB (b : Box) (x y : Nat) (hx : x < 64) :
    (innerMaskB b).testBit (64 * y + x) = true →
      b.y0 < y ∧ y < b.y1 ∧ y ≤ 62 ∧ b.x0 < x ∧ x < b.x1 ∧ x ≤ 62 := by
  unfold innerMaskB
  rw [testBit_maskRows (maskC_lt _ _) _ _ _ _ hx, testBit_maskC]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

/-! ## Bits of the closure test -/

/-- `allFrom` from a statement about every index of the range. -/
theorem allFrom_of_forall {p : Nat → Bool} {i k : Nat} (h : ∀ j, i ≤ j → j < i + k → p j = true) :
    allFrom p i k = true := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    simp only [allFrom, Bool.and_eq_true]
    exact ⟨h i (le_refl _) (by omega), ih (fun j h1 h2 => h j (by omega) (by omega))⟩

theorem testBit_of_and_eq {a b q : Nat} (h : a &&& b = a) (ha : a.testBit q = true) : b.testBit q = true := by
  have := congrArg (fun n => Nat.testBit n q) h
  simp only [Nat.testBit_and, ha, Bool.true_and] at this
  exact this

theorem memB_true {v x y : Nat} (h : memB v x y = true) : x < 63 ∧ y < 63 ∧ v.testBit (64 * y + x) = true := by
  simp only [memB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem memB_of_testBit {v x y : Nat} (hx : x < 63) (hy : y < 63) (h : v.testBit (64 * y + x) = true) :
    memB v x y = true := by
  simp [memB, hx, hy, h]

/-- The bit-parallel closure test implies the audited `closedIn` on the grids. -/
theorem closedB_closedIn {blk R : Nat} {b : Box} (hx1 : b.x1 ≤ 62) (hy1 : b.y1 ≤ 62) (h : closedB blk R b = true) :
    closedIn (toGrid blk) (toGrid R) b = true := by
  unfold closedB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  -- every cell of `R` in the box is strictly inside, with its four neighbours blocked or in `R`
  have key : ∀ x y, b.x0 ≤ x → x ≤ b.x1 → b.y0 ≤ y → y ≤ b.y1 → memB R x y = true →
      b.x0 < x ∧ x < b.x1 ∧ b.y0 < y ∧ y < b.y1 ∧
      (memB blk (x + 1) y || memB R (x + 1) y) = true ∧ (memB blk (x - 1) y || memB R (x - 1) y) = true ∧
      (memB blk x (y + 1) || memB R x (y + 1)) = true ∧ (memB blk x (y - 1) || memB R x (y - 1)) = true := by
    intro x y hx0 hx1' hy0 hy1' hm
    obtain ⟨hx, hy, hR⟩ := memB_true hm
    have hRb : (R &&& boxMaskB b).testBit (64 * y + x) = true := by
      rw [Nat.testBit_and, hR, testBit_boxMaskB b x y (by omega)]
      simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
      omega
    have hin := testBit_innerMaskB b x y (by omega) (testBit_of_and_eq h1 hRb)
    obtain ⟨hy0', hy1'', -, hx0', hx1'', -⟩ := hin
    -- the neighbour bits of `Rb`
    have hnb : ∀ q, ((R &&& boxMaskB b) <<< 1 ||| (R &&& boxMaskB b) >>> 1 ||| (R &&& boxMaskB b) <<< 64 |||
        (R &&& boxMaskB b) >>> 64).testBit q = true → (blk ||| R).testBit q = true :=
      fun q hq => testBit_of_and_eq h2 hq
    have s1 : ((R &&& boxMaskB b) <<< 1).testBit (64 * y + (x + 1)) = true := by
      rw [Nat.testBit_shiftLeft, show 64 * y + (x + 1) - 1 = 64 * y + x by omega, hRb]
      simp only [Bool.and_true, decide_eq_true_eq]
      omega
    have s2 : ((R &&& boxMaskB b) >>> 1).testBit (64 * y + (x - 1)) = true := by
      rw [Nat.testBit_shiftRight, show 1 + (64 * y + (x - 1)) = 64 * y + x by omega]
      exact hRb
    have s3 : ((R &&& boxMaskB b) <<< 64).testBit (64 * (y + 1) + x) = true := by
      rw [Nat.testBit_shiftLeft, show 64 * (y + 1) + x - 64 = 64 * y + x by omega, hRb]
      simp only [Bool.and_true, decide_eq_true_eq]
      omega
    have s4 : ((R &&& boxMaskB b) >>> 64).testBit (64 * (y - 1) + x) = true := by
      rw [Nat.testBit_shiftRight, show 64 + (64 * (y - 1) + x) = 64 * y + x by omega]
      exact hRb
    have n1 : (blk ||| R).testBit (64 * y + (x + 1)) = true := hnb _ (by simp [Nat.testBit_or, s1])
    have n2 : (blk ||| R).testBit (64 * y + (x - 1)) = true := hnb _ (by simp [Nat.testBit_or, s2])
    have n3 : (blk ||| R).testBit (64 * (y + 1) + x) = true := hnb _ (by simp [Nat.testBit_or, s3])
    have n4 : (blk ||| R).testBit (64 * (y - 1) + x) = true := hnb _ (by simp [Nat.testBit_or, s4])
    refine ⟨hx0', hx1'', hy0', hy1'', ?_, ?_, ?_, ?_⟩
    · rw [Nat.testBit_or] at n1
      simp only [memB, show x + 1 < 63 by omega, hy, decide_true, Bool.true_and]
      exact n1
    · rw [Nat.testBit_or] at n2
      simp only [memB, show x - 1 < 63 by omega, hy, decide_true, Bool.true_and]
      exact n2
    · rw [Nat.testBit_or] at n3
      simp only [memB, hx, show y + 1 < 63 by omega, decide_true, Bool.true_and]
      exact n3
    · rw [Nat.testBit_or] at n4
      simp only [memB, hx, show y - 1 < 63 by omega, decide_true, Bool.true_and]
      exact n4
  unfold closedIn
  apply allFrom_of_forall
  intro y hy0 hy1'
  simp only [Bool.or_eq_true]
  right
  apply allFrom_of_forall
  intro x hx0 hx1'
  simp only [memN_toGrid, okN, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq]
  by_cases hm : memB R x y = true
  · right
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := key x y hx0 (by omega) hy0 (by omega) hm
    simp only [Bool.or_eq_true] at a5 a6 a7 a8
    exact ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩
  · left
    simpa using hm

/-! ## Confinement on bitboards (as `confined_parts`, `reach_of_confined`, `not_connInf_of_confined`) -/

theorem confinedB_parts {blk R : Nat} {b : Box} {x y : Nat} (h : confinedB blk R b x y = true) :
    b.x1 ≤ 62 ∧ b.y1 ≤ 62 ∧ cellOf x y ∈ RSet (toGrid R) b ∧ closedIn (toGrid blk) (toGrid R) b = true := by
  simp only [confinedB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, ⟨x, y, rfl, h3, h4, h5, h6, by rw [memN_toGrid]; exact h7⟩, closedB_closedIn h1 h2 h8⟩

theorem reach_of_confinedB {blk R : Nat} {b : Box} {X : Set Cell} (hblk : BlockedIn (toGrid blk) X) {x y : Nat}
    (h : confinedB blk R b x y = true) : ∀ w, Reach X (cellOf x y) w → w ∈ RSet (toGrid R) b := by
  obtain ⟨h1, h2, h3, h4⟩ := confinedB_parts h
  intro w hw
  exact reach_subset h1 h2 hblk h4 h3 w hw.2

theorem not_connInf_of_confinedB {blk R : Nat} {b : Box} {X : Set Cell} (hblk : BlockedIn (toGrid blk) X)
    {x y : Nat} (h : confinedB blk R b x y = true) : ¬ ConnInf X (cellOf x y) := by
  intro hc
  obtain ⟨w, hwF, hw⟩ := hc ((Finset.Icc b.x0 b.x1 ×ˢ Finset.Icc b.y0 b.y1).image fun p => cellOf p.1 p.2)
  exact hwF (rset_finite (toGrid R) b (reach_of_confinedB hblk h w hw))

end Saw38a
