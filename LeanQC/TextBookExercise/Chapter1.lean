import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.NormNum

-- 1.3.11. Exercises

-- 1
example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 := by
  rw [h2, h1]
  ring

example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  calc
    y = 4 * x - 3 := h2
    _ = 4 * 3 - 3 := by rw [h1]
    _ = 12 - 3 := by ring
    _ = 9 := by ring

-- 2
example {a b : ℤ} (h : a - b = 0) : a = b :=
  calc
    a = a - b + b := by simp
    _ = 0 + b := by rw [h]
    _ = b := by simp

-- 3
example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  calc
    x = x - 3 * y + 3 * y := by ring
    _ = 5 + 3 * y := by rw [h1]
    _ = 5 + 3 * 3 := by rw [h2]
    _ = 5 + 9 := by ring
    _ = 14 := by ring

-- 4
example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 :=
  calc
    p = p - 2 * q + 2 * q := by ring
    _ = 1 + 2 * q := by rw [h1]
    _ = 1 + 2 * (-1) := by rw [h2]
    _ = 1 - 2 := by ring
    _ = -1 := by ring

-- 5
example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 :=
  calc
    x = x + 2 * y - 2 * y := by ring
    _ = 3 - 2 * y := by rw [h2]
    _ = 3 - 2 * (y + 1 - 1) := by ring
    _ = 3 - 2 * (3 - 1) := by rw [h1]
    _ = 3 - 2 * 2 := by ring
    _ = 3 - 4 := by ring
    _ = -1 := by ring

-- 6
example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 :=
  calc
    p = p + 4 * q - 4 * q := by ring
    _ = 1 - 4 * q := by rw [h1]
    _ = 1 - 4 * (q - 1 + 1) := by ring
    _ = 1 - 4 * (2 + 1) := by rw [h2]
    _ = 1 - 4 * 3 := by ring
    _ = 1 - 12 := by ring
    _ = -11 := by ring


-- 1.4.11

-- 1
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  calc
    x = x + 3 - 3 := by ring
    _ ≥ 2 * y - 3 := by rel[h1]
    _ ≥ 2 * 1 - 3 := by rel[h2]
    _ = 2 - 3 := by ring
    _ = -1 := by ring

-- 2
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  calc
    a + b = (a + (a + 2 * b))/2 := by ring
    _ ≥ (a + 4)/2:= by rel[h2]
    _ ≥ (3 + 4)/2 := by rel[h1]
    _ = 7/2 := by ring
    _ ≥ 3 := by norm_num

-- 3
example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x = x * (x ^ 2 - 8 * x + 2) := by ring
    _ = x * (x * (x - 8) + 2) := by ring
    _ ≥ 9 * (9 * (9 - 8) + 2) := by rel[hx]
    _ = 9 * (9 * 1 + 2) := by ring
    _ = 9 * 11 := by ring
    _ = 99 := by ring
    _ ≥ 3 := by norm_num

-- 4
example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
  calc
    n ^ 4 - 2 * n ^ 2 = n ^ 4 - n ^ 3 + n ^ 3 - 2 * n ^ 2 := by ring
    _ = n ^ 4 - n ^ 3 + n ^ 2 * (n - 2) := by ring
    _ ≥ n ^ 4 - n ^ 3 + 10 ^ 2 * (10 - 2) := by rel[hn]
    _ = n ^ 4 - n ^ 3 + 100 * 8 := by ring
    _ = n ^ 4 - n ^ 3 + 800 := by ring
    _ > n ^ 4 - n ^ 3 := by norm_num
    _ = n ^ 3 * (n - 1) := by ring
    _ ≥ n ^ 3 * (10 - 1) := by rel[hn]
    _ = n ^ 3 * 9 := by ring
    _ = 9 * n ^ 3 := by ring
    _ = 3 * n ^ 3 + 6 * n ^ 3:= by ring
    _ ≥ 3 * n ^ 3 + 6 * 10 ^ 3 := by rel[hn]
    _ = 3 * n ^ 3 + 6000 := by ring
    _ > 3 * n ^ 3 := by norm_num
