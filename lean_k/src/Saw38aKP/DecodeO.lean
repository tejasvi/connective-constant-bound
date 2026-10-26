import Saw38aKP.Grid

/-!
# Decoding in offset coordinates

`decodeO n T = (decode n T).map (List.map offC)`: the walk at offset 64 never truncates (a state has at most 40
cells), `small64` at offset 64 is `small`, `nodupO` is `nodupC` on small cells, and `shift33` returns offset 31.
-/

namespace Saw38a

open Saw38aCore Saw38aK

/-- Offset-64 coordinates of a cell. -/
def f64 (c : Cell) : Nat × Nat := ((c.1 + 64).toNat, (c.2 + 64).toNat)

/-- The unit step with direction index `i`. -/
def dirI (i : Nat) : Cell := if i = 0 then (1, 0) else if i = 1 then (0, 1) else if i = 2 then (-1, 0) else (0, -1)

theorem turnIdx_lt {t i : Nat} (hi : i < 4) : turnIdx t i < 4 := by
  unfold turnIdx; split_ifs <;> omega

theorem turnBack_dirI {t i : Nat} (hi : i < 4) : turnBack t (dirI i) = dirI (turnIdx t i) := by
  unfold turnBack turnIdx
  by_cases h1 : t = 1
  · interval_cases i <;> simp [h1, dirI]
  · by_cases h2 : t = 2
    · interval_cases i <;> simp [h2, dirI]
    · simp [h1, h2]

theorem dirI_bounds (i : Nat) : -1 ≤ (dirI i).1 ∧ (dirI i).1 ≤ 1 ∧ -1 ≤ (dirI i).2 ∧ (dirI i).2 ≤ 1 := by
  unfold dirI; split_ifs <;> simp

theorem stepBack_f64 {i : Nat} (hi : i < 4) {c : Cell} (h1 : 1 ≤ c.1 + 64) (h2 : 1 ≤ c.2 + 64) :
    stepBack i (f64 c) = f64 (c.1 - (dirI i).1, c.2 - (dirI i).2) := by
  obtain ⟨a, b⟩ := c
  simp only at h1 h2
  interval_cases i <;> refine Prod.ext ?_ ?_ <;> simp [stepBack, f64, dirI] <;> omega

theorem backO_eq (ts : List Nat) : ∀ (i : Nat) (c : Cell) (acc : List Cell), i < 4 →
    (ts.length : ℤ) < c.1 + 64 → (ts.length : ℤ) < c.2 + 64 →
    backO i (f64 c) ts (acc.map f64) = (back (dirI i) c ts acc).map f64 := by
  induction ts with
  | nil => intro i c acc _ _ _; simp [backO, back]
  | cons t ts ih =>
    intro i c acc hi h1 h2
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h1 h2
    simp only [backO, back]
    rw [turnBack_dirI hi, stepBack_f64 (turnIdx_lt hi) (by omega) (by omega)]
    obtain ⟨b1, b2, b3, b4⟩ := dirI_bounds (turnIdx t i)
    have := ih (turnIdx t i) (c.1 - (dirI (turnIdx t i)).1, c.2 - (dirI (turnIdx t i)).2)
      ((c.1 - (dirI (turnIdx t i)).1, c.2 - (dirI (turnIdx t i)).2) :: acc) (turnIdx_lt hi)
      (by simp only; omega) (by simp only; omega)
    simpa using this

theorem digitsQ_length (k : Nat) : ∀ T, (digitsQ k T).1.length = k := by
  induction k with
  | zero => intro T; rfl
  | succ k ih => intro T; simp [digitsQ, ih]

theorem pathO_eq {n T : Nat} (hn : n ≤ 40) :
    backO 0 (63, 64) (digitsQ (n - 2) T).1 [(63, 64), (64, 64)] = (pathOf n T).map f64 := by
  have e : backO 0 (63, 64) (digitsQ (n - 2) T).1 [(63, 64), (64, 64)] =
      backO 0 (f64 (-1, 0)) (digitsQ (n - 2) T).1 ([((-1 : Int), (0 : Int)), (0, 0)].map f64) := rfl
  have e' : pathOf n T = back (dirI 0) (-1, 0) (digitsQ (n - 2) T).1 [(-1, 0), (0, 0)] := rfl
  rw [e, e']
  have hl := digitsQ_length (n - 2) T
  exact backO_eq _ 0 (-1, 0) _ (by norm_num) (by simp only [hl]; omega) (by simp only [hl]; omega)

theorem small64_f64 (c : Cell) : small64 (f64 c) = small c := by
  obtain ⟨a, b⟩ := c
  show small64 ((a + 64).toNat, (b + 64).toNat) = small (a, b)
  rw [Bool.eq_iff_iff]
  simp only [small64, small, Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> intro h <;> omega

theorem nodupO_map (p : List Cell) (hp : ∀ c ∈ p, small c = true) : nodupO (p.map f64) = nodupC p := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    simp only [List.map_cons, nodupO, nodupC, List.all_map]
    rw [ih (fun d hd => hp d (List.mem_cons_of_mem _ hd))]
    congr 1
    have hc := hp c List.mem_cons_self
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, Function.comp]
    constructor
    · intro H d hd
      have hd' := hp d (List.mem_cons_of_mem _ hd)
      have := H d hd
      obtain ⟨a, b⟩ := c
      obtain ⟨a', b'⟩ := d
      simp only [small, Bool.and_eq_true, decide_eq_true_eq] at hc hd'
      simp only [f64, Bool.or_eq_true, bne_iff_ne, ne_eq] at this ⊢
      omega
    · intro H d hd
      have hd' := hp d (List.mem_cons_of_mem _ hd)
      have := H d hd
      obtain ⟨a, b⟩ := c
      obtain ⟨a', b'⟩ := d
      simp only [small, Bool.and_eq_true, decide_eq_true_eq] at hc hd'
      simp only [f64, Bool.or_eq_true, bne_iff_ne, ne_eq] at this ⊢
      omega

theorem shift33_f64 {c : Cell} (hc : small c = true) : shift33 (f64 c) = offC c := by
  obtain ⟨a, b⟩ := c
  simp only [small, Bool.and_eq_true, decide_eq_true_eq] at hc
  refine Prod.ext ?_ ?_ <;> simp [shift33, f64, offC, ox] <;> omega

/-- Decoding in offset coordinates is decoding followed by `offC`. -/
theorem decodeO_eq (n T : Nat) : decodeO n T = (decode n T).map (List.map offC) := by
  unfold decodeO decode
  by_cases h1 : (n < 2 || 40 < n) = true
  · rw [if_pos h1, if_pos h1]; rfl
  · have hn : n ≤ 40 := by simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h1; omega
    rw [if_neg h1, if_neg h1]
    by_cases h2 : ((digitsQ (n - 2) T).2 != 0) = true
    · rw [if_pos h2, if_pos h2]; rfl
    · rw [if_neg h2, if_neg h2]
      dsimp only
      rw [pathO_eq hn]
      by_cases h3 : (pathOf n T).all small = true
      · have hs : ∀ c ∈ pathOf n T, small c = true := List.all_eq_true.1 h3
        have h3' : ((pathOf n T).map f64).all small64 = true := by
          rw [List.all_map]; simpa [Function.comp_def, small64_f64] using h3
        rw [nodupO_map _ hs, h3', h3]
        by_cases h4 : nodupC (pathOf n T) = true
        · rw [h4, Bool.and_self, if_pos rfl, if_pos rfl, Option.map_some, List.map_map]
          congr 1
          apply List.map_congr_left
          intro c hc
          exact shift33_f64 (hs c hc)
        · have h4' : nodupC (pathOf n T) = false := by simpa using h4
          rw [h4', Bool.and_false]
          simp
      · have h3f : (pathOf n T).all small = false := by simpa using h3
        have h3' : ((pathOf n T).map f64).all small64 = false := by
          rw [List.all_map]; simpa [Function.comp_def, small64_f64] using h3
        rw [h3', h3f, Bool.false_and, Bool.false_and]
        simp

end Saw38a
