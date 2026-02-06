
import Mathlib
set_option maxHeartbeats 0
set_option autoImplicit false
set_option pp.numericTypes true
set_option pp.coercions true
set_option pp.letVarTypes true
set_option pp.structureInstanceTypes true
set_option pp.instanceTypes true
set_option pp.mvars.withType true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
open scoped BigOperators
open Real Nat Topology Rat Filter Finset Set


theorem odd_product_implies_a_eq_one (a b c d : ℕ) (ha_pos : 0 < a) (hb_pos : 0 < b) (hc_pos : 0 < c) (hd_pos : 0 < d)
    (ha_odd : Odd a) (hb_odd : Odd b) (hc_odd : Odd c) (hd_odd : Odd d)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hprod : a * d = b * c)
    (k m : ℤ) (had_sum : a + d = 2 ^ k) (hbc_sum : b + c = 2 ^ m) : a = 1 := sorry

theorem inequality_proof : ∀ (a b : ℝ), |a + b| / (1 + |a + b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := sorry

theorem multiplicative_inverse_problem (n : ℤ) (hn1 : 0 ≤ n) (hn2 : n < 1399) (h : (35 : ℤ) * 40 = 1400) : n = 1058 ∧ n * 160 ≡ 1 [ZMOD 1399] := sorry

theorem not_prime_sum (K L M N : ℕ) (hK : K > 0) (hL : L > 0) (hM : M > 0) (hN : N > 0) 
  (hKL : K > L) (hLM : L > M) (hMN : M > N) 
  (h_eq : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) : 
  ¬ Nat.Prime (K * L + M * N) := sorry

theorem inequality_for_positive_reals : ∀ (x y z : ℝ), x > 0 → y > 0 → z > 0 → 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := sorry

theorem congruence_problem (n : ℤ) (h : (2 * n) ≡ 15 [ZMOD 47]) : n ≡ 31 [ZMOD 47] := sorry

theorem solve_mod_equation : ∀ (b : ℤ), 0 ≤ b → b ≤ 120 → 24 * b ≡ 1 [ZMOD 121] → b = 116 := sorry

theorem linear_system_solution (x y z : ℝ) (h1 : 3 * x + y = 17) (h2 : 5 * y + z = 14) (h3 : 3 * x + 5 * z = 41) : x + y + z = 12 := sorry

theorem goal_statement : 
    let f : ℤ → ℤ := λ n => if Odd n then n ^ 2 else n ^ 2 - 4 * n - 1
    let a : ℤ := 4 in
    f (f (f (f (f a)))) = 1 := sorry

theorem perfect_square_expression (n : ℤ) (hn : n ≥ 9) : 
    ∃ (k : ℤ), ((n + 2)! - (n + 1)!) / n! = k ^ 2 := sorry

theorem exists_irrational_power_irrational_rational : ∃ (a b : ℝ), Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := sorry

theorem gcd_properties_and_k_value :
    ∀ (k : ℕ) (hk : k > 0),
    (∀ (n : ℕ) (hn : n > 0), Nat.gcd (6 * n + k) (6 * n + 3) = 1) →
    (∀ (n : ℕ) (hn : n > 0), Nat.gcd (6 * n + k) (6 * n + 2) = 1) →
    (∀ (n : ℕ) (hn : n > 0), Nat.gcd (6 * n + k) (6 * n + 1) = 1) →
    k = 5 ∧ ∀ (m : ℕ) (hm : m > 0) (hmlt : m < 5), ∃ (n : ℕ) (hn : n > 0),
      (Nat.gcd (6 * n + m) (6 * n + 3) > 1) ∨ (Nat.gcd (6 * n + m) (6 * n + 2) > 1) ∨ (Nat.gcd (6 * n + m) (6 * n + 1) > 1) := sorry

theorem count_even_digit_divisible_by_five : 
    let D : Set ℕ := {x | 1000 ≤ x ∧ x < 10000} in
    let E : Set ℕ := {0, 2, 4, 6, 8} in
    Finset.card (Finset.filter (λ x => 
      let d1 := x / 1000 in
      let d2 := (x / 100) % 10 in
      let d3 := (x / 10) % 10 in
      let d4 := x % 10 in
      d1 ∈ ({2, 4, 6, 8} : Set ℕ) ∧ d2 ∈ E ∧ d3 ∈ E ∧ d4 ∈ E ∧ (d4 = 0 ∨ d4 = 5))
    (Finset.Icc 1000 9999)) = 100 := sorry

theorem product_of_sums_is_21000 :
    let S₁ := ∑ k in Finset.Icc 1 20, Real.logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ (k ^ 2))
    let S₂ := ∑ k in Finset.Icc 1 100, Real.logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k)
    let P := S₁ * S₂ in
    P = 21000 := sorry

theorem sum_reciprocal_sqrt_bound : ∀ (f : ℝ → ℝ) (hf : ∀ x, f x = 1 / Real.sqrt x), (∑ k in Finset.Icc 2 10000, f (k : ℝ)) < 198 := sorry

theorem smallest_n_with_gcd_gt_one : ∃ n : ℕ, 0 < n ∧ (∀ m : ℕ, 0 < m → m < n → Nat.gcd ((m : ℕ)^2 - m + 41) (((m : ℕ) + 1)^2 - (m + 1) + 41) = 1) ∧ Nat.gcd ((n : ℕ)^2 - n + 41) (((n : ℕ) + 1)^2 - (n + 1) + 41) > 1 ∧ n = 41 := sorry

theorem polynomial_identity_goal (A B : ℤ) (h : ∀ x, 10 * x ^ 2 - x - 24 = (A * x - 8) * (B * x + 3)) : A * B + B = 12 := sorry

theorem inequality_proof (a : ℝ) (b : ℝ) (ha : a > 0) (hb : b > 0) (hle : b ≤ a) :
    (a + b)/2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := sorry

theorem count_perfect_square_divisors : 
    let n : ℕ := 9 in
    let a : ℕ → ℕ := λ k => Nat.factorial k in
    let P : ℕ := ∏ i in Finset.Icc 1 n, a i in
    let perfect_squares : Finset ℕ := {d | ∃ (k : ℕ), d = k ^ 2} in
    let square_divisors : Finset ℕ := {d | d ∣ P ∧ d ∈ perfect_squares} in
    Finset.card square_divisors = 672 := sorry

theorem exists_infinitely_many_m_n_inequality : ∀ (k : ℕ), ∃ (m : ℕ), m > 0 ∧ k ≤ m ∧ ∃ (n : ℕ), n > 0 ∧ m * n ≤ m + n := sorry

theorem complex_current_calculation (V I Z : ℂ) (hV : V = 1 + Complex.I) (hZ : Z = 2 - Complex.I) (hEquation : V = I * Z) : I = (1/5 : ℂ) + (3/5 : ℂ) * Complex.I := sorry

theorem not_necessarily_n_gt_84 : ¬∀ (n : ℕ), n > 0 → (1/2 + 1/3 + 1/7 + 1/(n : ℕ) : ℚ) ∈ ℤ → n > 84 := sorry

theorem remainder_of_power_eq_one : (5 : ℤ) ^ (30 : ℕ) % (7 : ℤ) = 1 := sorry

theorem gcd_lcm_implies_n_eq_70 (n : ℕ) (hn_pos : n > 0) (h_gcd : Nat.gcd n 40 = 10) (h_lcm : Nat.lcm n 40 = 280) : n = 70 := sorry

theorem product_identity_equivalence :
    ∀ (k : ℕ) (a b : ℝ), a = 2 → b = 3 → 
    let P := (a + b) * (a ^ 2 + b ^ 2) * (a ^ 4 + b ^ 4) * (a ^ 8 + b ^ 8) * (a ^ 16 + b ^ 16) * (a ^ 32 + b ^ 32) * (a ^ 64 + b ^ 64)
    in P = b ^ 128 - a ^ 128 := sorry

theorem compute_product_abc (a b c : ℝ) (P : ℝ → ℝ) (hP : ∀ x, P x = x^3 + a * x^2 + b * x + c) 
    (hroots : ∀ x, P x = 0 ↔ x = Real.cos (2 * π / 7) ∨ x = Real.cos (4 * π / 7) ∨ x = Real.cos (6 * π / 7)) : 
    a * b * c = 1/8 := sorry

theorem arithmetic_progression_sum_of_even_terms :
    ∀ (a : ℕ → ℝ) (d : ℝ), d = 1 → 
    let n : ℕ := 98 in
    let sum_total : ℝ := ∑ i in Finset.range n, a (i + 1) in
    sum_total = 137 → 
    let sum_even_terms : ℝ := ∑ i in Finset.range 49, a (2 * (i + 1)) in
    sum_even_terms = 93 := sorry

theorem intersection_sum_eq_four :
    ∀ (x y : ℝ), (3 * y = x) → (2 * x + 5 * y = 11) → (x + y = 4) := sorry

theorem prime_divides_a_pow_p_minus_a (p : ℕ) (hp : Nat.Prime p) (a : ℕ) (ha : a > 0) : p ∣ a ^ p - a := sorry

theorem f_neg_for_x5 : f (25/11 : ℚ) < 0 := sorry

theorem sqrt_equation_implies_a_eq_8 (a : ℝ) (h : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) : a = 8 := sorry

theorem product_plus_difference_le_one (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : a * b + (a - b) ≤ 1 := sorry

theorem floor_sum_equals_3702 : 
    let N : ℝ := 1/3 in
    let X : ℝ := N in
    (Int.floor (10 * N) : ℤ) + (Int.floor (100 * N) : ℤ) + (Int.floor (1000 * N) : ℤ) + (Int.floor (10000 * N) : ℤ) = 3702 := sorry

theorem inequality_proof (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) :
    (a ^ 2 / b) + (b ^ 2 / c) + (c ^ 2 / d) + (d ^ 2 / a) ≥ a + b + c + d := sorry

theorem units_digit_p_eq_8 : (Nat.digits 10 (16^17 * 17^18 * 18^19)).head? = some 8 := sorry

theorem number_of_solutions : 
    let solutions : Set ℝ := {x | x ∈ Set.Icc (0 : ℝ) π ∧ Real.sin ((π/2) * Real.cos x) = Real.cos ((π/2) * Real.sin x)}
    in Fintype.card (Subtype solutions) = 2 := sorry

theorem maximum_value_of_f : 
    ∃ (t : ℝ), (∀ (x : ℝ), ((2^x - 3*x) * x) / (4^x) ≤ ((2^t - 3*t) * t) / (4^t)) ∧ ((2^t - 3*t) * t) / (4^t) = 1/12 := sorry

theorem minimum_at_seven : ∀ (x : ℝ), f 7 ≤ f x := by
  intro x
  have f_def : ∀ (x : ℝ), f x = x ^ 2 - 14 * x + 3 := by
    intro x
    rfl
  rw [f_def, f_def]
  have h : x ^ 2 - 14 * x + 3 - (7 ^ 2 - 14 * 7 + 3) = (x - 7) ^ 2 := by
    ring
  linarith
  done

theorem largest_sum_of_distinct_positive_factors_of_2001 :
    ∀ (I M O : ℕ) (hI : I > 0) (hM : M > 0) (hO : O > 0) 
    (hdistinct : I ≠ M ∧ I ≠ O ∧ M ≠ O) (hprod : I * M * O = 2001),
    I + M + O ≤ 671 := sorry

theorem tan_eq_cos_solutions_count : 
    let f : ℝ → ℝ := λ x => Real.tan (2 * x) - Real.cos (x / 2) in
    Finset.card (Finset.filter (λ x => Real.tan (2 * x) = Real.cos (x / 2)) 
      (Finset.Icc (0 : ℝ) (2 * π) : Finset ℝ)) = 5 := sorry

theorem least_sum_of_m_n (m : ℕ) (n : ℕ) (hm : m > 0) (hn : n > 0) 
    (h_gcd : Nat.gcd m n = 8) (h_lcm : Nat.lcm m n = 112) : 
    72 ≤ m + n ∧ ∃ (m' : ℕ) (n' : ℕ), m' > 0 ∧ n' > 0 ∧ Nat.gcd m' n' = 8 ∧ 
    Nat.lcm m' n' = 112 ∧ m' + n' = 72 := sorry

theorem last_three_digits_sum_eq_13 : 
    let n : ℕ := 100
    let b : ℕ := 5
    let S : ℕ := b ^ n
    in ∀ (d2 d1 d0 : ℕ), 
      d2 < 10 → d1 < 10 → d0 < 10 → 
      S % 1000 = 100 * d2 + 10 * d1 + d0 → 
      d2 + d1 + d0 = 13 := sorry

theorem parity_sequence : 
    let D : ℕ → ℕ := fun n => match n with
      | 0 => 0
      | 1 => 0
      | 2 => 1
      | k + 3 => D (k + 2) + D k
    in
    Even (D 2021) ∧ Odd (D 2022) ∧ Even (D 2023) := sorry

theorem power_bound (n : ℕ) (hn : n > 0) : (n : ℝ) ^ ((1 : ℝ) / (n : ℝ)) ≤ 2 - (1 : ℝ) / (n : ℝ) := sorry

theorem product_abc_is_720 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a * (b + c) = 152) (h2 : b * (c + a) = 162) (h3 : c * (a + b) = 170) :
    a * b * c = 720 := sorry

theorem remainder_computation : (1529 : ℤ) % (6 : ℤ) = (5 : ℤ) := sorry

theorem square_of_ninety_one : (91 : ℕ)^2 = 8281 := sorry

theorem log_base_3_of_27_eq_3 : Real.logb (3 : ℝ) (27 : ℝ) = (3 : ℝ) := sorry

theorem solve_for_a (h : a ≠ 0) (h_eq : (8⁻¹ : ℝ) / (4⁻¹ : ℝ) - a⁻¹ = (1 : ℝ)) : a = -2 := sorry

theorem complex_equation_solution (z : ℂ) (h : 12 * ‖z‖^2 = ‖2 * z + 2‖^2 + ‖z^2 + 1‖^2 + 31) : z + 6 / z = -2 := sorry

theorem arithmetic_geometric_means_squared_sum :
    ∀ (x y : ℝ), (x + y) / 2 = 7 → Real.sqrt (x * y) = Real.sqrt 19 → x ^ 2 + y ^ 2 = 158 := sorry

theorem cube_root_identity (r : ℝ) (hpos : r > 0) (h : r ^ (1/3 : ℝ) + 1 / (r ^ (1/3 : ℝ)) = 3) : r ^ 3 + 1 / (r ^ 3) = 5778 := sorry

theorem exists_unique_initial_condition : ∃! (x₁ : ℝ), 0 < x₁ ∧ ∀ (n : ℕ), n > 0 → let x := Nat.rec x₁ (λ k xₖ => xₖ * (xₖ + 1 / (k : ℝ))) n in 0 < x ∧ x < Nat.rec x₁ (λ k xₖ => xₖ * (xₖ + 1 / (k : ℝ))) (n + 1) ∧ Nat.rec x₁ (λ k xₖ => xₖ * (xₖ + 1 / (k : ℝ))) (n + 1) < 1 := sorry

theorem maximum_distance_between_sets :
    let A : Set ℂ := {z | z ^ 3 - 8 = 0}
    let B : Set ℂ := {z | z ^ 3 - 8 * z ^ 2 - 8 * z + 64 = 0}
    in sSup {d | ∃ a ∈ A, ∃ b ∈ B, d = Complex.dist a b} = 2 * Real.sqrt 21 := sorry

theorem exists_int_divisible_by_eleven (n : ℕ) : ∃ (k : ℤ), (10 : ℤ)^n - ((-1 : ℤ))^n = 11 * k := sorry

theorem product_bound (n : ℕ) (hn : n > 0) (a : ℕ → ℝ) (ha_nonneg : ∀ i, 0 ≤ a i) (hsum : ∑ i in Finset.Icc 1 n, a i = n) : 
    ∏ i in Finset.Icc 1 n, a i ≤ 1 := sorry

theorem log_square_computation (x y : ℝ) (hx_pos : x > 0) (hx_ne_one : x ≠ 1) (hy_pos : y > 0) (hy_ne_one : y ≠ 1)
    (h_log_eq : Real.logb 2 x = Real.logb y 16) (h_product : x * y = 64) :
    (Real.logb 2 (x / y)) ^ 2 = 20 := sorry

theorem solve_for_c (c x : ℝ) (h : f c 2 = 9) : c = 3 := sorry

theorem inequality_proof (x : ℝ) (n : ℕ) (hx : x > -1) : 1 + (n : ℝ) * x ≤ (1 + x) ^ n := sorry

theorem congruence_result : ∃ n : ℤ, 0 ≤ n ∧ n < 101 ∧ (123456 : ℤ) ≡ n [ZMOD 101] ∧ n = 34 := sorry

theorem son_age_six (f s : ℕ) (hf : f > 0) (hs : s > 0) (h1 : f = 5 * s) (h2 : (f - 3) + (s - 3) = 30) : s = 6 := sorry

theorem arithmetic_series_sum_proof (a d : ℝ) (S : ℕ → ℝ) (hS : ∀ n, S n = (n : ℝ) / 2 * (2 * a + ((n : ℝ) - 1) * d)) (hS5 : S 5 = 70) (hS10 : S 10 = 210) : a = 42/5 := sorry

theorem residue_mod_four : (121 : ℤ) * 122 * 123 % 4 = 2 := sorry

theorem sum_one_to_twelve_mod_four : (∑ i in Finset.Icc 1 12, i) % 4 = 2 := sorry

theorem expression_evaluation : ∀ (x : ℝ), x = 4 → (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * 4 * x + 1 = 11 := sorry

theorem sum_of_solutions : ∑ x : ℝ in {x : ℝ | |2 - x| = 3}, x = 4 := sorry

theorem product_of_real_roots_eq_20 : ∀ (x : ℝ), x^2 + 18*x + 30 = 2 * Real.sqrt (x^2 + 18*x + 45) → 
    let roots := {y : ℝ | y^2 + 18*y + 30 = 2 * Real.sqrt (y^2 + 18*y + 45)}
    in ∏ y in roots, y = 20 := sorry

theorem f_value_at_three (a b : ℝ) (f : ℝ → ℝ) (h1 : ∀ x : ℝ, f x = a * x ^ 4 - b * x ^ 2 + x + 5) (h2 : f (-3) = 2) : f 3 = 8 :=
  sorry

theorem solve_system :
    ∀ (a b c d : ℕ),
      a > 0 → b > 0 → c > 0 → d > 0 →
      a * b * c * d = 40320 →
      a * b + a + b = 524 →
      b * c + b + c = 146 →
      c * d + c + d = 104 →
      a - d = 10 := sorry

theorem base3_1222_to_base10_is_53 : (1 * 3^3 + 2 * 3^2 + 2 * 3^1 + 2 * 3^0 : ℕ) = 53 := sorry

theorem remainder_property (n : ℕ) (hn : n > 0) : (3^(2^n) - 1) % (2^(n + 3)) = 2^(n + 2) := sorry

theorem arithmetic_sequence_problem (a d : ℝ) (T : ℕ → ℝ) (hT : ∀ n : ℕ, T (n + 1) = a + (n : ℝ) * d) (hT7 : T 7 = 30) (hT11 : T 11 = 60) : T 21 = 135 := sorry

theorem f_84_eq_997 : f 84 = 997 := sorry

theorem find_functions : ∀ (f : ℤ → ℤ), (∀ (a b : ℤ), f (2 * a) + 2 * f b = f (f (a + b))) → ?_ := sorry

theorem compute_f_g_at_two : f (g 2) = 8 := sorry

theorem ordered_pair_equality (a b : ℝ) (h1 : 3 * a + 2 * b = 5) (h2 : a + b = 2) : (a, b) = (1, 1) := sorry

theorem prime_product_minus_sum_eq_119 : ∃ a b : ℕ, a ∈ ({5, 7, 11, 13, 17} : Set ℕ) ∧ b ∈ ({5, 7, 11, 13, 17} : Set ℕ) ∧ a ≠ b ∧ ((a : ℝ) * (b : ℝ) - ((a : ℝ) + (b : ℝ)) = (119 : ℝ)) := sorry

theorem marble_problem : R = 6 := sorry

theorem f_14_52_eq_364 : f 14 52 = 364 := sorry

theorem cube_root_expression_eq_four (a : ℝ) (h : a = 8) : (16 * Real.rpow (a ^ 2) (1/3 : ℝ)) ^ (1/3 : ℝ) = 4 := sorry

theorem radical_simplification (x : ℝ) (hx : x ≥ 0) : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 6 * Real.sqrt (210) * x := sorry

theorem jasmine_water_consumption (d w : ℝ) (h : w = 1.5 * (d / 3)) : w + 5 = 1.5 * ((d + 10) / 3) := sorry

theorem number_of_zeros : 
    let f (θ : ℝ) : ℝ := 1 - 3 * Real.sin θ + 5 * Real.cos (3 * θ) in
    Finset.card (Finset.filter (λ θ => f θ = 0) (Set.Ioc (0 : ℝ) (2 * π) : Finset ℝ)) = 6 := sorry

theorem log_equality : 
    let a : ℝ := 2 in
    let b : ℝ := 3 in
    let x : ℝ := 6 in
    a > 0 ∧ a ≠ 1 ∧ b > 0 ∧ b ≠ 1 ∧ x > 0 →
    let log_a_x := Real.logb a x in
    let log_b_x := Real.logb b x in
    let log_a_b := Real.logb a b in
    let log_b_a := Real.logb b a in
    let E := Real.sqrt (log_a_x + log_b_x) in
    let D := Real.sqrt (log_a_b) + Real.sqrt (log_b_a) in
    E = D := sorry

theorem inequality_power_mean (a : ℝ) (b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) (hn : 0 < n) : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := sorry

theorem power_sum_equation (a b x y : ℝ) (h1 : a * x + b * y = 3) (h2 : a * x ^ 2 + b * y ^ 2 = 7) 
    (h3 : a * x ^ 3 + b * y ^ 3 = 16) (h4 : a * x ^ 4 + b * y ^ 4 = 42) : 
    a * x ^ 5 + b * y ^ 5 = 20 := sorry

theorem periodic_function_existence (a : ℝ) (ha : a > 0) (f : ℝ → ℝ) 
    (hf : ∀ x : ℝ, f (x + a) = 1/2 + Real.sqrt (f x - (f x)^2)) : 
    ∃ (b : ℝ), b > 0 ∧ ∀ x : ℝ, f (x + b) = f x := sorry

theorem units_digit_is_two : (Int.ofNat ((29 * 79) + (31 * 81))).toNat % 10 = 2 := sorry

theorem remainder_computation : (194 : ℤ) % (11 : ℤ) = (7 : ℤ) := sorry

theorem bounds_on_real_numbers (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : a + b + c = 2) (h4 : a * b + b * c + c * a = 1) : 
    0 ≤ a ∧ a ≤ 1/3 ∧ 1/3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4/3 := sorry

theorem integer_solutions_absolute_value_inequality : Finset.card (Finset.filter (λ (x : ℤ) => |(x : ℝ)| < 3 * Real.pi) Finset.univ) = 19 := sorry

theorem find_difference (a b : ℕ) (hsum : a + b = 17402) (hdiv : 10 ∣ a) (d : ℤ) (hd_range : 0 ≤ d ∧ d ≤ 9) 
    (hunits : (a / 10 : ℕ) = b) : a - b = 15458 := sorry

theorem sequence_problem (h : a₁ : ℝ) (h : b₁ : ℝ) (h : ∀ n : ℕ, (a (n + 1), b (n + 1)) = (Real.sqrt 3 * a n - b n, Real.sqrt 3 * b n + a n)) (h : (a 100, b 100) = (2 : ℝ, 4 : ℝ)) : a₁ + b₁ = (1 : ℝ) / (2 : ℝ)^(98 : ℕ) := sorry

theorem prime_sum_equation (m n : ℕ) (hm : Nat.Prime m) (hn : Nat.Prime n) (k t : ℕ) (hk_pos : k > 0) (ht_pos : t > 0) 
    (h_ineq : k > t) (h_roots : ∀ x : ℕ, x^2 - m * x + n = 0 ↔ x = k ∨ x = t) : m^n + n^m + k^t + t^k = 20 := sorry

theorem greater_even_integer_is_eighteen (n : ℕ) (hn : n > 0) : 
    let first_even := 2 * n
    let second_even := 2 * n + 2
    in first_even * second_even = 288 → max first_even second_even = 18 := sorry

theorem sum_of_special_reals_eq_sqrt_five (a : ℝ) (b : ℝ) (ha_pos : 0 < a) (hb_pos : 0 < b) (h_ne : a ≠ b) 
    (h_a : |a - 1/a| = 1) (h_b : |b - 1/b| = 1) : a + b = Real.sqrt 5 := sorry

theorem triangle_inequality_expression (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) 
    (h1 : a + b > c) (h2 : a + c > b) (h3 : b + c > a) : 
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := sorry

theorem polynomial_coefficient_B :
    ∀ (A B C D : ℝ) (r : Fin 6 → ℕ),
    (∀ i, 0 < r i) →
    (Polynomial.monic (Polynomial.ofFinsupp (Finsupp.single 0 (16 : ℂ) + Finsupp.single 1 (D : ℂ) + Finsupp.single 2 (C : ℂ) + Finsupp.single 3 (B : ℂ) + Finsupp.single 4 (A : ℂ) + Finsupp.single 5 (-10 : ℂ) + Finsupp.single 6 (1 : ℂ)))) ∧
    (Polynomial.roots (Polynomial.ofFinsupp (Finsupp.single 0 (16 : ℂ) + Finsupp.single 1 (D : ℂ) + Finsupp.single 2 (C : ℂ) + Finsupp.single 3 (B : ℂ) + Finsupp.single 4 (A : ℂ) + Finsupp.single 5 (-10 : ℂ) + Finsupp.single 6 (1 : ℂ)))) = 
     Multiset.map (fun i : Fin 6 => (r i : ℂ)) Finset.univ.val) →
    B = -88 := sorry

theorem sum_of_a_and_b : ∀ (a b : ℝ), a ^ 2 * b ^ 3 = 32/27 → a / b ^ 3 = 27/4 → a + b = 8/3 := sorry

theorem arithmetic_sequence_nth_term :
    ∀ (x d : ℝ) (a₁ a₂ a₃ : ℝ) (n : ℕ),
      a₁ = 2 * x - 3 →
      a₂ = 5 * x - 11 →
      a₃ = 3 * x + 1 →
      a₂ - a₁ = d →
      a₃ - a₂ = d →
      n > 0 →
      (∃ (seq : ℕ → ℝ), seq 0 = a₁ ∧ ∀ k, seq (k + 1) = seq k + d ∧ seq (n - 1) = 2009) →
      n = 502 := sorry

