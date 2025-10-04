import Mathlib
open scoped BigOperators
open Real Topology Filter

/-
Natural‑language prompts → Lean statements
Each theorem is named P<n>_* matching your list’s numbering.
-/

/- 1 -/
theorem P1_am_gm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  sorry

/- 2 -/
theorem P2_quad_solutions (x : ℝ) :
    x ^ 2 - 5 * x + 6 = 0 ↔ x = 2 ∨ x = 3 := by
  sorry

/- 3 -/
theorem P3_sum_1_to_n (n : ℕ) :
    ∑ k in Finset.range (n + 1), k = n * (n + 1) / 2 := by
  sorry

/- 4 -/
theorem P4_log1p_lt (x : ℝ) (hx : 0 < x) :
    Real.log (1 + x) < x := by
  sorry

/- 5 -/
theorem P5_deriv_poly :
    deriv (fun x : ℝ => x ^ 3 + 3 * x ^ 2 - 2 * x + 1)
      = (fun x => 3 * x ^ 2 + 6 * x - 2) := by
  sorry

/- 6 -/
theorem P6_int_x2 :
    ∫ x in (0 : ℝ)..1, x ^ 2 = (1 : ℝ) / 3 := by
  sorry

/- 7 (note: from 1/p + 1/q = 1 over ℚ we get p=q=2 hence product = 1) -/
theorem P7_recip_sum_one (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h : (1 : ℚ) / p + 1 / q = 1) :
    (p - 1) * (q - 1) = 1 := by
  sorry

/- 8 -/
theorem P8_gcd_lcm (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Nat.gcd a b * Nat.lcm a b = a * b := by
  simpa using Nat.gcd_mul_lcm a b

/- 9 -/
theorem P9_tendsto_one_over_n :
    Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) := by
  sorry

/- 10  (correct value is 58) -/
theorem P10_a2b2 (a b : ℝ) (h₀ : a + b = 10) (h₁ : a * b = 21) :
    a ^ 2 + b ^ 2 = 58 := by
  sorry

/- 11  (true for n ≥ 2) -/
theorem P11_pow2_gt (n : ℕ) (hn : 2 ≤ n) :
    (2 : ℕ) ^ n > n + 1 := by
  sorry

/- 12 -/
theorem P12_rows_dep {A : Matrix (Fin 2) (Fin 2) ℝ}
    (h : A.det = 0) :
    ∃ (c₁ c₂ : ℝ), (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧
      (c₁ • A 0 + c₂ • A 1) = 0 := by
  /- rows linearly dependent -/
  sorry

/- 13 -/
theorem P13_deriv_sin : deriv Real.sin = Real.cos := by
  sorry

/- 14 -/
theorem P14_lim_sin_over_x :
    Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[≠] 0) (𝓝 1) := by
  sorry

/- 15 -/
theorem P15_sqrt2_irrational : Irrational (Real.sqrt 2) := by
  sorry

/- 16 -/
theorem P16_deriv_pos_strictMono
    (f : ℝ → ℝ) {a b : ℝ} (h : a ≤ b)
    (hderiv : ∀ x ∈ Set.Icc a b, deriv f x > 0) :
    StrictMonoOn f (Set.Icc a b) := by
  sorry

/- 17 -/
theorem P17_choose_symm (n k : ℕ) :
    Nat.choose n k = Nat.choose n (n - k) := by
  sorry

/- 18  (correct value is 26) -/
theorem P18_x2y2 (x y : ℝ) (h₀ : x + y = 6) (h₁ : x * y = 5) :
    x ^ 2 + y ^ 2 = 26 := by
  sorry

/- 19 -/
theorem P19_binom_sq (a b : ℝ) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  sorry

/- 20  (definite integral form) -/
theorem P20_int_exp (a b : ℝ) :
    ∫ x in a..b, Real.exp x = Real.exp b - Real.exp a := by
  sorry

/- 21 -/
theorem P21_harmonic_gt_log (n : ℕ) (hn : 1 ≤ n) :
    (∑ k in Finset.Icc 1 n, (1 : ℝ) / k) > Real.log (n + 1) := by
  sorry

/- 22 -/
theorem P22_circle_3_4 (x y : ℝ) (h₀ : x ^ 2 + y ^ 2 = 25) (hx : x = 3) :
    y = 4 ∨ y = -4 := by
  sorry

/- 23 -/
theorem P23_odd_sq (n : ℕ) :
    Nat.Odd n → Nat.Odd (n ^ 2) := by
  sorry

/- 24  (Maclaurin series existence at 0) -/
theorem P24_sin_has_series :
    HasFPowerSeriesAt Real.sin Real.sinPowerSeries 0 := by
  simpa using Real.hasFPowerSeriesAt_sin

/- 25 -/
theorem P25_infinite_primes :
    Set.Infinite {p : ℕ | Nat.Prime p} := by
  simpa using Nat.infinite_setOf_prime

/- 26 -/
theorem P26_abs_3_4i :
    Complex.abs (3 + 4 * Complex.I : ℂ) = 5 := by
  sorry

/- 27  (geometry; classical statement stub) -/
theorem P27_triangle_angle_sum
    {P₁ P₂ P₃ : EuclideanSpace ℝ (Fin 2)}
    (h : ¬ AffineSubspace.Collinear ℝ ({P₁, P₂, P₃} : Set _)) :
    angle P₂ P₁ P₃ + angle P₁ P₂ P₃ + angle P₁ P₃ P₂ = Real.pi := by
  sorry

/- 28 -/
theorem P28_strict_am_gm (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    (a + b) / 2 > Real.sqrt (a * b) := by
  sorry

/- 29 -/
theorem P29_int_sin_0_pi :
    ∫ x in (0 : ℝ)..Real.pi, Real.sin x = 2 := by
  sorry

/- 30 -/
theorem P30_fact_gt_pow (n : ℕ) (hn : 4 ≤ n) :
    Nat.factorial n > 2 ^ n := by
  sorry

/- 31  (eigenvalues 3 and 1 exist) -/
open Matrix in
theorem P31_eigs_2x2 :
    ∃ v₁ : ℝ × ℝ, v₁ ≠ 0 ∧ (!![2,1;1,2] : Matrix (Fin 2) (Fin 2) ℝ) *
      ![v₁.1, v₁.2] = (3 : ℝ) • ![v₁.1, v₁.2]
  ∧ ∃ v₂ : ℝ × ℝ, v₂ ≠ 0 ∧ (!![2,1;1,2] : Matrix (Fin 2) (Fin 2) ℝ) *
      ![v₂.1, v₂.2] = (1 : ℝ) • ![v₂.1, v₂.2] := by
  sorry

/- 32 -/
theorem P32_trig_id (x : ℝ) :
    Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := by
  simpa using Real.cos_sq_add_sin_sq x

/- 33 -/
theorem P33_convex_from_second_deriv
    (f : ℝ → ℝ) (h : ∀ x, deriv (deriv f) x ≥ 0) :
    Convex ℝ (Set.univ) → ConvexOn ℝ (Set.univ) f := by
  /- skeleton: one standard route uses second derivative ≥ 0 → convex -/
  sorry

/- 34 -/
theorem P34_sum_choose (n : ℕ) :
    (∑ k in Finset.range (n + 1), Nat.choose n k) = 2 ^ n := by
  sorry

/- 35 -/
theorem P35_int_log_0_1 :
    ∫ x in (0 : ℝ)..1, Real.log x = -1 := by
  sorry

/- 36 -/
theorem P36_root_interval :
    ∃ r : ℝ, (r ^ 3 - 2 * r + 4 = 0) ∧ (-2 < r ∧ r < -1) := by
  sorry

/- 37  (area under x^2 from 0 to 3) -/
theorem P37_area_0_3 :
    ∫ x in (0 : ℝ)..3, x ^ 2 = 9 := by
  sorry

/- 38 -/
theorem P38_limit_n_over_n1 :
    Tendsto (fun n : ℕ => (n : ℝ) / (n + 1)) atTop (𝓝 1) := by
  sorry

/- 39 -/
theorem P39_exp_gt_tangent (x : ℝ) (hx : 0 < x) :
    Real.exp x > 1 + x := by
  sorry

/- 40 -/
theorem P40_int_cos_0_pi2 :
    ∫ x in (0 : ℝ)..(Real.pi / 2), Real.cos x = 1 := by
  sorry

/- 41 -/
theorem P41_geom_series (a : ℝ) (h : |a| < 1) :
    ∑' n : ℕ, a ^ n = 1 / (1 - a) := by
  sorry

/- 42 -/
theorem P42_inv_inv {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) [Invertible A] :
    ((A⁻¹)⁻¹ : Matrix n n ℝ) = A := by
  simpa using inv_inv A

/- 43  (divergence of curl = 0; placeholder) -/
-- NOTE: A full formalization requires vector calculus framework.
theorem P43_div_curl_zero_placeholder : True := by
  trivial

/- 44 -/
theorem P44_x2_nonneg (x : ℝ) : 0 ≤ x ^ 2 := by
  have := sq_nonneg x; simpa [pow_two] using this

/- 45 -/
theorem P45_deriv_log :
    deriv Real.log = fun x => 1 / x := by
  -- understood as equality on ℝ\{0}; mathlib has `deriv_log`
  sorry

/- 46 -/
theorem P46_exp_strictMono :
    StrictMono (Real.exp) := by
  simpa using Real.strictMono_exp

/- 47 -/
theorem P47_deriv_x_pow_x :
    DifferentiableOn ℝ (fun x : ℝ => x ^ x) (Set.Ioi 0) ∧
    deriv (fun x : ℝ => x ^ x) = fun x => x ^ x * (Real.log x + 1) := by
  sorry

/- 48 -/
theorem P48_deriv_inv :
    deriv (fun x : ℝ => (1 : ℝ) / x) = fun x => -1 / x ^ 2 := by
  sorry

/- 49 -/
theorem P49_int_one_minus_x :
    ∫ x in (0 : ℝ)..1, (1 - x) = (1 : ℝ) / 2 := by
  sorry
