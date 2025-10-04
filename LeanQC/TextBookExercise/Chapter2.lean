import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic


-- 2.1.9 Exercises

-- 1
example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 : x ^ 2 + 2 * x = 4 + 2 * x := by rw[h1]
  have h4 : x ^ 2 + 2 * x = x * (x + 2) := by ring
  have h5 : 4 + 2 * x = 2 * (x + 2) := by ring
  have h6 : x * (x + 2) = 4 + 2 * x := by
    rw[h4] at h3
    exact h3
  have h7 : x * (x + 2) = 2 * (x + 2) := by
    rw[h5] at h6
    exact h6
  simp_all only [mul_eq_mul_right_iff, h1]
  rcases h7 with hx2 | hxneg
  · exact hx2
  · linarith      -- since x > 1, x + 2 = 0 is impossible

-- 2
example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by
  have h1 :=
    calc
      (n - 2) ^ 2 = n ^ 2 - 4 * n + 4 := by ring
      _ = 0 := by linarith
  simp_all only [zero_lt_two, pow_eq_zero_iff]
  linarith

-- 3
example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by
  have hx : x ≠ 0 := by linarith
  have hy : y = 1 / x := by exact eq_one_div_of_mul_eq_one_right h
  simp_all only [one_div, ne_eq, not_false_eq_true, mul_inv_cancel, ge_iff_le]
  exact inv_le_one h2


-- 2.2.4 Exercises

-- 1
example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt
  have : 3 * m = 12 := by linarith
  linarith

-- 2
example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  apply le_antisymm
  . linarith
  . linarith


-- 2.3.6 Exercises

-- 1
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain rfl | rfl := h
  · norm_num
  · norm_num

-- 2
example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain rfl | rfl := h
  · norm_num
  · norm_num

-- 5
example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  linarith


-- 2.4.5 Exercises

-- 1
example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨ha, hab⟩ := H
  have h1 : 2 * a + b = (a + b) + a := by ring
  have h2 : (a + b) + a ≤ 3 + 1 := by linarith
  rw [h1]
  linarith

-- 2
example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨hr, hs⟩ := H
  have h2 : (r + s) + (r - s) ≤ 6 := by linarith
  linarith

-- 4
example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  -- Step 1: derive p ≥ 7
  have h1 : p ≥ 7 := by linarith
  -- Step 2: split the ∧ goal
  constructor
  · -- Goal: p ^ 2 ≥ 49
    calc
      p ^ 2 ≥ 7 ^ 2 := by gcongr    -- from p ≥ 7 and monotonicity of square
      _ = 49 := by norm_num
  · -- Goal: 7 ≤ p
    exact h1


-- 2.5.9 Exercises

-- 1
example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  norm_num

-- 2
example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 9, 2
  norm_num

-- 6
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, ha⟩ := h
  sorry
