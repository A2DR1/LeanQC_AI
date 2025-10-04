import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic


-- 4.1.10 Exercises

-- 1
example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  -- 1. Instantiate the ∀ with b = 2
  specialize h 2
  -- h : a ≥ -3 + 4*2 - 2^2
  -- 2. Compute the right-hand side using `norm_num`
  norm_num at h
  -- h : a ≥ 1
  -- 3. Conclude
  exact h

-- 2
-- example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
--   -- 1. Instantiate the hypothesis for m = 3 and m = 5
--   have h3 : 3 ∣ n := by
--     apply hn 3
--     · norm_num        -- 1 ≤ 3
--     · norm_num        -- 3 ≤ 5

--   have h5 : 5 ∣ n := by
--     apply hn 5
--     · norm_num        -- 1 ≤ 5
--     · norm_num        -- 5 ≤ 5

--   -- 2. Combine divisibility
--   have h15 : 15 ∣ n := by
--     library_search

-- 3
example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  -- 1. Use `exists` to introduce n
  existsi 0
  -- 2. Prove the property for all m
  intro m
  -- 3. Use `norm_num` to show that 0 ≤ m
  norm_num

-- 4
example : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  use 0                 -- choose a = 0
  intro b               -- fix an arbitrary b
  use b + 1             -- choose c = b + 1
  norm_num              -- 0 + b < b + 1

-- 5
-- example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
--   sorry

-- 6
example : ¬ Prime 45 := by
  sorry
