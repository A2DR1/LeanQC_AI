import Generated._Header

/-- 1. Binomial expansion for (x + 1)². -/
theorem P1_binomial (x : ℝ) :
    (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by
  ring

/-- 2. Square of a real number is nonnegative. -/
theorem P2_sq_nonneg (x : ℝ) : 0 ≤ x ^ 2 := by
  exact sq_nonneg x

/-- 3. Sum of first n natural numbers. -/
theorem P3_sum_nat (n : ℕ) :
    ∑ i in Finset.range (n + 1), i = n * (n + 1) / 2 := by
  simp [Finset.sum_range_id, Nat.mul_div_cancel]

/-- 4. Cosine–sine identity. -/
theorem P4_trig_identity (x : ℝ) :
    Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := by
  simpa using Real.cos_sq_add_sin_sq x

/-- 5. Derivative of x² is 2x. -/
theorem P5_deriv_square :
    deriv (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
  funext x
  simp [deriv_pow]

/-- 6. Product of gcd and lcm equals product of numbers. -/
theorem P6_gcd_lcm (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Nat.gcd a b * Nat.lcm a b = a * b := by
  simpa using Nat.gcd_mul_lcm a b

/-- 7. If n is odd, then n² is odd. -/
theorem P7_odd_sq {n : ℕ} (h : Odd n) : Odd (n ^ 2) := by
  exact Nat.odd_mul.mpr ⟨h, h⟩

/-- 8. For all reals, (a + b)² = a² + 2ab + b². -/
theorem P8_binomial2 (a b : ℝ) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

/-- 9. For any real x, x * 0 = 0. -/
theorem P9_mul_zero (x : ℝ) : x * 0 = 0 := by
  simp

/-- 10. If x > 0, then log(1+x) < x. -/
theorem P10_log_lt (x : ℝ) (hx : 0 < x) : Real.log (1 + x) < x := by
  apply Real.log_one_add_lt_self hx
