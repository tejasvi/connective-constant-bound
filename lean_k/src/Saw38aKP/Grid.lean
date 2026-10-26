import Saw38a.CheckMain
import Saw38aK.CheckB2

/-!
# Bitboards versus the audited grids

`toGrid v` is the 63-row grid of a bitboard. Bit tests on `v` are `memN` queries on `toGrid v`; `setB` and `gridB`
match `setN` and `gridOf` exactly (as arrays); offset cells match the audited `Cell` arithmetic for small cells.
-/

namespace Saw38a

open Saw38aCore Saw38aK

/-! ## Rows of a bitboard -/

theorem testBit_M63 (i : Nat) : Nat.testBit 9223372036854775807 i = decide (i < 63) := by
  rw [show (9223372036854775807 : Nat) = 2 ^ 63 - 1 by norm_num, Nat.testBit_two_pow_sub_one]

theorem rowsOfBB_length (v k : Nat) : (rowsOfBB v k).length = k := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => simp [rowsOfBB, ih]

theorem rowsOfBB_getElem (k : Nat) : ∀ (v y : Nat) (h : y < (rowsOfBB v k).length),
    (rowsOfBB v k)[y] = (v >>> (64 * y)) &&& 9223372036854775807 := by
  induction k with
  | zero => intro v y h; simp [rowsOfBB] at h
  | succ k ih =>
    intro v y h
    cases y with
    | zero => simp [rowsOfBB]
    | succ y =>
      simp only [rowsOfBB, List.getElem_cons_succ]
      rw [ih (v >>> 64) y (by simp [rowsOfBB, rowsOfBB_length] at h ⊢; omega), ← Nat.shiftRight_add]
      congr 2
      ring

theorem toGrid_size (v : Nat) : (toGrid v).size = 63 := by
  simp [toGrid, gridOfBB, rowsOfBB_length]

theorem toGrid_getElem (v y : Nat) (h : y < (toGrid v).size) :
    (toGrid v)[y] = (v >>> (64 * y)) &&& 9223372036854775807 :=
  rowsOfBB_getElem 63 v y (by simpa [toGrid, gridOfBB] using h)

theorem gok_toGrid (v : Nat) : GOK (toGrid v) := toGrid_size v

/-- Bit tests are `memN` queries. -/
theorem memN_toGrid (v x y : Nat) : memN (toGrid v) x y = memB v x y := by
  unfold memN memB
  by_cases hy : y < 63
  · rw [getElem!_pos (toGrid v) y (by rw [toGrid_size]; exact hy), toGrid_getElem]
    simp only [Nat.testBit_and, Nat.testBit_shiftRight, testBit_M63, hy, decide_true, Bool.and_true]
    rw [Bool.and_comm]
  · rw [getElem!_neg (toGrid v) y (by rw [toGrid_size]; exact hy)]
    simp [hy]

theorem toGrid_zero : toGrid 0 = emptyG := by decide

theorem toGrid_setB {v x y : Nat} (hx : x < 63) (hy : y < 63) : toGrid (setB v x y) = setN (toGrid v) x y := by
  apply Array.ext
  · simp [setN, toGrid_size]
  · intro i h1 h2
    simp only [setN, Array.getElem_modify]
    rw [toGrid_getElem, toGrid_getElem]
    apply Nat.eq_of_testBit_eq
    intro j
    split_ifs with hyi
    · subst hyi
      simp only [setB, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, testBit_M63, Nat.testBit_two_pow,
        pow2_eq hx]
      by_cases hj : j < 63 <;> by_cases hxj : x = j <;> simp [hj, hxj] <;> omega
    · simp only [setB, Nat.testBit_and, Nat.testBit_or, Nat.testBit_shiftRight, testBit_M63, Nat.testBit_two_pow]
      by_cases hj : j < 63
      · have : ¬ (64 * y + x = 64 * i + j) := by omega
        simp [hj, this]
      · simp [hj]

theorem add_eq_setN {g : Grid} {c : Cell} (h : inRange c = true) : add g c = setN g (ox c.1) (ox c.2) := by
  simp [add, h]

theorem ox_lt_of_inRange {c : Cell} (h : inRange c = true) : ox c.1 < 63 ∧ ox c.2 < 63 := by
  rw [inRange_iff] at h
  exact ⟨ox_lt h.1 h.2.1, ox_lt h.2.2.1 h.2.2.2⟩

theorem toGrid_setB_add {v : Nat} {c : Cell} (h : inRange c = true) :
    toGrid (setB v (offC c).1 (offC c).2) = add (toGrid v) c := by
  obtain ⟨h1, h2⟩ := ox_lt_of_inRange h
  rw [add_eq_setN h]
  exact toGrid_setB h1 h2

theorem toGrid_foldl (S : List Cell) (hS : ∀ c ∈ S, inRange c = true) : ∀ (v : Nat) (g : Grid), toGrid v = g →
    toGrid ((S.map offC).foldl (fun v c => setB v c.1 c.2) v) = S.foldl add g := by
  induction S with
  | nil => intro v g h; simpa using h
  | cons c S ih =>
    intro v g h
    simp only [List.map_cons, List.foldl_cons]
    apply ih (fun d hd => hS d (List.mem_cons_of_mem _ hd))
    rw [toGrid_setB_add (hS c (List.mem_cons_self ..)), h]

/-- The bitboard of a list of in-range cells is its grid. -/
theorem toGrid_gridB (S : List Cell) (hS : ∀ c ∈ S, inRange c = true) : toGrid (gridB (S.map offC)) = gridOf S :=
  toGrid_foldl S hS 0 emptyG toGrid_zero

theorem memO_offC {v : Nat} {c : Cell} (h : inRange c = true) : memO v (offC c) = mem (toGrid v) c := by
  simp [memO, offC, mem, h, memN_toGrid]

theorem cellOfK_eq (x y : Nat) : cellOfK x y = cellOf x y := rfl

theorem inRange_of_small' {c : Cell} (h : small c = true) : inRange c = true := inRange_of_small h

theorem small_inRange {S : List Cell} (hS : Small S) : ∀ c ∈ S, inRange c = true :=
  fun c hc => inRange_of_small (hS c hc)

/-! ## Offset arithmetic -/

theorem stepO_eq {t : Nat} (ht : t < 3) : stepO t = offC (stepC t) := by
  interval_cases t <;> decide

theorem bboxO_map (S : List Cell) (e : Nat) : bboxO (S.map offC) e = bboxE S e := by
  simp [bboxO, bboxE, List.map_map, Function.comp_def, offC]

theorem offC_addC_d4c {g : Nat} (hg : g < 8) {z t : Cell} (hz : small z = true)
    (ht : t = (1, 0) ∨ t = (0, 1) ∨ t = (0, -1)) :
    addO (d4o g (offC z)) (offC t) = offC (addC (d4c g z) t) := by
  obtain ⟨a, b⟩ := z
  simp only [small, Bool.and_eq_true, decide_eq_true_eq] at hz
  rcases ht with rfl | rfl | rfl <;> interval_cases g <;>
    refine Prod.ext ?_ ?_ <;> simp [addO, d4o, offC, addC, d4c, ox] <;> omega

theorem inRange_addC_d4c {g : Nat} (hg : g < 8) {z t : Cell} (hz : small z = true)
    (ht : t = (1, 0) ∨ t = (0, 1) ∨ t = (0, -1)) : inRange (addC (d4c g z) t) = true := by
  obtain ⟨a, b⟩ := z
  simp only [small, Bool.and_eq_true, decide_eq_true_eq] at hz
  rcases ht with rfl | rfl | rfl <;> interval_cases g <;> simp [inRange, addC, d4c] <;> omega

/-- The offsets of `g z + t` (small `z`, step `t`) lie in `[2, 60]`. -/
theorem offC_addC_d4c_range {g : Nat} (hg : g < 8) {z t : Cell} (hz : small z = true)
    (ht : t = (1, 0) ∨ t = (0, 1) ∨ t = (0, -1)) :
    2 ≤ (offC (addC (d4c g z) t)).1 ∧ (offC (addC (d4c g z) t)).1 ≤ 60 ∧
    2 ≤ (offC (addC (d4c g z) t)).2 ∧ (offC (addC (d4c g z) t)).2 ≤ 60 := by
  obtain ⟨a, b⟩ := z
  simp only [small, Bool.and_eq_true, decide_eq_true_eq] at hz
  rcases ht with rfl | rfl | rfl <;> interval_cases g <;> simp [offC, addC, d4c, ox] <;> omega

end Saw38a
