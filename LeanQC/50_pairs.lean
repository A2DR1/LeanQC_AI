import Mathlib
open scoped BigOperators
open Real Nat Topology Filter

/-- 1. AM–GM inequality for two positives --/
theorem P1_am_gm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by sorry

/-- 2. Solutions of quadratic x^2 - 5x + 6 = 0 --/
theorem P2_quad_roots (x : ℝ) :
    x ^ 2 - 5 * x + 6 = 0 ↔ x = 2 ∨ x = 3 := by sorry

/-- 3. Sum of first n natural numbers --/
theorem P3_sum_1_to_n (n : ℕ) :
    ∑ k in Finset.range (n + 1), k = n * (n + 1) / 2 := by sorry

/-- 4. log(1+x) < x for positive x --/
theorem P4_log1p_lt (x : ℝ) (hx : 0 < x) :
    Real.log (1 + x) < x := by sorry

/-- 5. Derivative of cubic polynomial --/
theorem P5_deriv_poly :
    deriv (fun x : ℝ => x ^ 3 + 3 * x ^ 2 - 2 * x + 1)
      = (fun x => 3 * x ^ 2 + 6 * x - 2) := by sorry

/-- 6. ∫₀¹ x² dx = 1/3 --/
theorem P6_int_x2 :
    ∫ x in (0 : ℝ)..1, x ^ 2 = (1 : ℝ) / 3 := by sorry

/-- 7. If 1/p + 1/q = 1 then (p-1)(q-1)=1 --/
theorem P7_recip_sum (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h : (1 : ℚ) / p + 1 / q = 1) :
    (p - 1) * (q - 1) = 1 := by sorry

/-- 8. gcd * lcm = product --/
theorem P8_gcd_lcm (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Nat.gcd a b * Nat.lcm a b = a * b := by sorry

/-- 9. Sequence 1/n tends to 0 --/
theorem P9_tendsto_inv_nat :
    Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) := by sorry

/-- 10. If a+b=10, ab=21, then a²+b²=58 --/
theorem P10_a2b2 (a b : ℝ) (h₀ : a + b = 10) (h₁ : a * b = 21) :
    a ^ 2 + b ^ 2 = 58 := by sorry

/-- 11. 2^n > n+1 for n≥2 --/
theorem P11_pow2_gt (n : ℕ) (hn : 2 ≤ n) :
    (2 : ℕ) ^ n > n + 1 := by sorry

/-- 12. 2x2 singular matrix rows are dependent --/
theorem P12_rows_dep {A : Matrix (Fin 2) (Fin 2) ℝ}
    (h : A.det = 0) :
    ∃ (c₁ c₂ : ℝ), (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ (c₁ • A 0 + c₂ • A 1) = 0 := by sorry

/-- 13. d/dx sin x = cos x --/
theorem P13_deriv_sin : deriv Real.sin = Real.cos := by sorry

/-- 14. lim x→0 sin x / x = 1 --/
theorem P14_lim_sin_over_x :
    Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by sorry

/-- 15. √2 is irrational --/
theorem P15_sqrt2_irrational : Irrational (Real.sqrt 2) := by sorry

/-- 16. If f' > 0 on interval then f is increasing --/
theorem P16_deriv_pos_increasing
    (f : ℝ → ℝ) {a b : ℝ} (h : a ≤ b)
    (hderiv : ∀ x ∈ Set.Icc a b, deriv f x > 0) :
    StrictMonoOn f (Set.Icc a b) := by sorry

/-- 17. Binomial symmetry choose n k = choose n (n-k) --/
theorem P17_choose_symm (n k : ℕ) :
    Nat.choose n k = Nat.choose n (n - k) := by sorry

/-- 18. If x+y=6, xy=5, then x²+y²=26 --/
theorem P18_x2y2 (x y : ℝ) (h₀ : x + y = 6) (h₁ : x * y = 5) :
    x ^ 2 + y ^ 2 = 26 := by sorry

/-- 19. (a+b)² expansion --/
theorem P19_binom_sq (a b : ℝ) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by sorry

/-- 20. ∫ exp from a to b = e^b - e^a --/
theorem P20_int_exp (a b : ℝ) :
    ∫ x in a..b, Real.exp x = Real.exp b - Real.exp a := by sorry

/-- 21. Harmonic series > log(n+1) --/
theorem P21_harmonic_gt_log (n : ℕ) (hn : 1 ≤ n) :
    (∑ k in Finset.Icc 1 n, (1 : ℝ) / k) > Real.log (n + 1) := by sorry

/-- 22. Circle x²+y²=25, x=3 → y=±4 --/
theorem P22_circle_3_4 (x y : ℝ) (h₀ : x ^ 2 + y ^ 2 = 25) (hx : x = 3) :
    y = 4 ∨ y = -4 := by sorry

/-- 23. If n is odd, then n² is odd. --/
theorem P23_odd_sq (n : ℕ) : Odd n → Odd (n ^ 2) := by sorry

/-- 24. The sine function admits a Maclaurin-series-type expansion at 0. --/
theorem P24_sin_series : Differentiable ℝ Real.sin := by sorry

/-- 25. Infinite primes --/
theorem P25_infinite_primes : Set.Infinite {p : ℕ | Nat.Prime p} := by sorry

/-- 26. |3+4i| = 5 --/
theorem P26_abs_3_4i : Complex.abs (3 + 4 * Complex.I : ℂ) = 5 := by sorry

/-- 27. Triangle sum of angles = π --/
theorem P27_triangle_angle_sum
    {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (h : A + B + C = Real.pi) :
    A + B + C = Real.pi := by sorry

/-- 28. Strict AM–GM for a>b>0 --/
theorem P28_strict_am_gm (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    (a + b) / 2 > Real.sqrt (a * b) := by sorry

/-- 29. ∫₀^π sin x dx = 2 --/
theorem P29_int_sin_pi : ∫ x in (0 : ℝ)..Real.pi, Real.sin x = 2 := by sorry

/-- 30. n! > 2ⁿ for n≥4 --/
theorem P30_fact_gt_pow (n : ℕ) (hn : 4 ≤ n) :
    Nat.factorial n > 2 ^ n := by sorry

/-- 31. For all real numbers x, (x + 1)² = x² + 2x + 1. -/
theorem algebra_binomial_square (x : ℝ) :
    (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by sorry

/-- 32. cos²x + sin²x = 1 --/
theorem P32_trig_id (x : ℝ) : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := by sorry

/-- 33. f″≥0 ⇒ f convex --/
theorem P33_convex_from_second_deriv (f : ℝ → ℝ)
    (h : ∀ x, deriv (deriv f) x ≥ 0) :
    ConvexOn ℝ Set.univ f := by sorry

/-- 34. ∑ₖ₌₀ⁿ C(n,k)=2ⁿ --/
theorem P34_sum_choose (n : ℕ) :
    (∑ k in Finset.range (n + 1), Nat.choose n k) = 2 ^ n := by sorry

/-- 35. ∫₀¹ log x dx = −1 --/
theorem P35_int_log_0_1 : ∫ x in (0 : ℝ)..1, Real.log x = -1 := by sorry

/-- 36. x³−2x+4=0 has root in (−2,−1) --/
theorem P36_root_interval : ∃ r : ℝ, r ^ 3 - 2 * r + 4 = 0 ∧ -2 < r ∧ r < -1 := by sorry

/-- 37. Area under x² from 0 to 3 = 9 --/
theorem P37_area_0_3 : ∫ x in (0 : ℝ)..3, x ^ 2 = 9 := by sorry

/-- 38. lim n→∞ n/(n+1)=1 --/
theorem P38_limit_n_over_n1 :
    Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by sorry

/-- 39. eˣ > 1+x for x>0 --/
theorem P39_exp_gt_tangent (x : ℝ) (hx : 0 < x) :
    Real.exp x > 1 + x := by sorry

/-- 40. ∫₀^{π/2} cos x dx = 1 --/
theorem P40_int_cos_0_pi2 : ∫ x in (0 : ℝ)..(Real.pi / 2), Real.cos x = 1 := by sorry

/-- 41. |a|<1 ⇒ ∑ aⁿ = 1/(1−a) --/
theorem P41_geom_series (a : ℝ) (h : |a| < 1) :
    ∑' n : ℕ, a ^ n = 1 / (1 - a) := by sorry

/-- 42. (A⁻¹)⁻¹ = A for invertible matrix --/
theorem P42_inv_inv {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) [Invertible A] :
    ((A⁻¹)⁻¹ : Matrix n n ℝ) = A := by sorry

/-- 43. ∇·(∇×F)=0 placeholder --/
theorem P43_div_curl_zero : True := by trivial

/-- 44. x²≥0 for all reals --/
theorem P44_x2_nonneg (x : ℝ) : 0 ≤ x ^ 2 := by sorry

/-- 45. d/dx log x = 1/x --/
theorem P45_deriv_log : deriv Real.log = fun x => 1 / x := by sorry

/-- 46. eˣ strictly increasing --/
theorem P46_exp_strictMono : StrictMono (Real.exp) := by sorry

/-- 47. d/dx xˣ = xˣ(log x + 1) --/
theorem P47_deriv_x_pow_x :
    DifferentiableOn ℝ (fun x : ℝ => x ^ x) (Set.Ioi 0) ∧
    deriv (fun x => x ^ x) = fun x => x ^ x * (Real.log x + 1) := by sorry

/-- 48. d/dx 1/x = −1/x² --/
theorem P48_deriv_inv : deriv (fun x : ℝ => (1 : ℝ) / x) = fun x => -1 / x ^ 2 := by sorry

/-- 49. ∫₀¹(1−x)dx=1/2 --/
theorem P49_int_one_minus_x : ∫ x in (0 : ℝ)..1, (1 - x) = (1 : ℝ) / 2 := by sorry

/-- 50. Continuous function on [a,b] attains max/min --/
theorem P50_extreme_value (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Set.Icc a b)) :
    ∃ x₁ x₂, x₁ ∈ Set.Icc a b ∧ x₂ ∈ Set.Icc a b ∧
      ∀ x ∈ Set.Icc a b, f x₁ ≤ f x ∧ f x ≤ f x₂ := by sorry
