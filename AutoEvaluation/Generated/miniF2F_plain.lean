-- import Mathlib
-- set_option maxHeartbeats 0
-- set_option autoImplicit false
-- set_option pp.numericTypes true
-- set_option pp.coercions true
-- set_option pp.letVarTypes true
-- set_option pp.structureInstanceTypes true
-- set_option pp.instanceTypes true
-- set_option pp.mvars.withType true
-- set_option pp.funBinderTypes true
-- set_option pp.piBinderTypes true
-- open scoped BigOperators
-- open Real Nat Topology Rat Filter Finset Set

-- theorem odd_integers_condition {a b c d : ℤ} (ha : Odd a) (hb : Odd b) (hc : Odd c) (hd : Odd d)
--     (hlt : 0 < a ∧ a < b ∧ b < c ∧ c < d) (had : a * d = b * c)
--     (h1 : ∃ (k : ℤ), a + d = 2 ^ k) (h2 : ∃ (m : ℤ), b + c = 2 ^ m) : a = 1 := sorry

-- theorem inequality_for_absolute_values (a b : ℝ) : |a + b| / (1 + |a + b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := sorry

-- theorem multiplicative_inverse_exists : ∃ n : ℕ, n < 1399 ∧ (160 * n) % 1399 = 1 := by
--   refine ⟨1058, ?_, ?_⟩
--   · omega
--   · native_decide

-- theorem not_prime_of_equation {K L M N : ℕ} (hK : K > 0) (hL : L > 0) (hM : M > 0) (hN : N > 0)
--   (h_order : K > L ∧ L > M ∧ M > N)
--   (h_eq : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) :
--   ¬ Nat.Prime (K * L + M * N) := sorry

-- theorem inequality_for_positive_reals (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
--     9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := sorry

-- theorem congruence_solution : ∃ n : ℕ, n < 47 ∧ 2 * n % 47 = 15 % 47 ∧ n = 31 := sorry

-- theorem find_modular_inverse : ∃ (b : ℕ), b < 11^2 ∧ (24 * b) % (11^2) = 1 ∧ b = 116 := sorry

-- theorem solve_system_sum : ∃ (x y z : ℝ), 3*x + y = 17 ∧ 5*y + z = 14 ∧ 3*x + 5*z = 41 ∧ x + y + z = 12 := sorry

-- theorem f_composition_result : f (f (f (f (f (4))))) = 1 := sorry

-- theorem perfect_square_for_n_ge_9 : ∀ (n : ℕ), n ≥ 9 → ∃ (k : ℕ), ((Nat.factorial (n + 2)) - (Nat.factorial (n + 1))) / (Nat.factorial n) = k ^ 2 := sorry

-- theorem exist_irrational_power_rational : ∃ (a b : ℝ), Irrational a ∧ Irrational b ∧ Rational (a ^ b) := sorry

-- theorem smallest_k_satisfies_condition :
--     (∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, 0 < n →
--       Nat.Coprime (6 * n + k) (6 * n + 3) ∧
--       Nat.Coprime (6 * n + k) (6 * n + 2) ∧
--       Nat.Coprime (6 * n + k) (6 * n + 1)) ∧
--     (∀ m : ℕ, 0 < m ∧ m < 5 →
--       ¬∀ n : ℕ, 0 < n →
--         Nat.Coprime (6 * n + m) (6 * n + 3) ∧
--         Nat.Coprime (6 * n + m) (6 * n + 2) ∧
--         Nat.Coprime (6 * n + m) (6 * n + 1)) := sorry

-- theorem count_4digit_even_digits_divisible_by_5 :
--     Finset.card (Finset.filter (λ n : ℕ ↦ 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d : ℕ, d ∈ (Nat.digits 10 n) → Even d) ∧ 5 ∣ n) (Finset.Icc 1000 9999)) = 100 := sorry

-- theorem log_sum_product_eq_21000 : (∑ k in Finset.Icc 1 20, Real.log (3^(k^2)) / Real.log ((5 : ℝ)^k)) * (∑ k in Finset.Icc 1 100, Real.log ((25 : ℝ)^k) / Real.log ((9 : ℝ)^k)) = (21000 : ℝ) := sorry

-- theorem sum_reciprocal_sqrt_lt_198 : ∑ k in Finset.Icc 2 10000, (1 : ℝ) / Real.sqrt k < 198 := sorry

-- theorem euler_polynomial_common_factor :
--     let p (n : ℕ) := n ^ 2 - n + 41 in
--     ∃ n : ℕ, 0 < n ∧ 1 < Nat.gcd (p n) (p (n + 1)) ∧
--     ∀ m < n, 0 < m → Nat.gcd (p m) (p (m + 1)) = 1 := sorry

-- theorem factor_problem : ∃ (A B : ℤ), (10 : ℤ) * x ^ 2 - x - 24 = (A * x - 8) * (B * x + 3) ∧ A * B + B = 12 := sorry

-- theorem inequality_proof (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : b ≤ a) : (a + b)/2 - Real.sqrt (a * b) ≤ (a - b)^2/(8 * b) := sorry

-- theorem perfect_square_divisors_count : Finset.card (Finset.filter (λ d : ℕ ↦ ∃ k : ℕ, d = k^2) (Nat.divisors (∏ i : ℕ in Finset.Icc 1 9, Nat.factorial i))) = 672 := sorry

-- theorem infinitely_many_m : Set.Infinite {m : ℕ | m > 0 ∧ ∃ n : ℕ, n > 0 ∧ m * n ≤ m + n} := sorry

-- theorem complex_current_calculation : (1 + Complex.I) / (2 - Complex.I) = (1/5 : ℂ) + (3/5 : ℂ) * Complex.I := sorry

-- theorem problem_statement : ∃ (n : ℕ) (hn : n > 0),
--     (1/2 : ℚ) + (1/3 : ℚ) + (1/7 : ℚ) + (1/(n : ℚ)) ∈ Set.range (Int.cast : ℤ → ℚ) ∧
--     ¬(2 ∣ n) ∧ ¬(3 ∣ n) ∧ ¬(6 ∣ n) ∧ ¬(7 ∣ n) ∧ ¬(n > 84) := sorry

-- theorem remainder_of_5_pow_30_div_7 : (5 ^ 30) % 7 = 1 := sorry

-- theorem find_n_gcd_lcm : ∃ n : ℕ, Nat.gcd n 40 = 10 ∧ Nat.lcm n 40 = 280 ∧ n = 70 := sorry

-- theorem product_equivalence : (∏ k in Finset.range 7, ((2 : ℝ) ^ (2^k) + (3 : ℝ) ^ (2^k))) = (3 : ℝ)^128 - (2 : ℝ)^128 := sorry

-- theorem polynomial_roots_cosine_identity :
--     let P : ℂ → ℂ := λ x => x^3 + a * x^2 + b * x + c
--     let roots : Set ℂ := {Complex.cos (2 * π / 7), Complex.cos (4 * π / 7), Complex.cos (6 * π / 7)}
--     in (∀ r ∈ roots, P r = 0) → a * b * c = 1/32 := sorry

-- theorem arithmetic_progression_sum_even_terms :
--     ∃ (a₁ : ℕ), ∀ (ap : ℕ → ℕ), (∀ n, ap (n + 1) = ap n + 1) ∧ (∑ i in Finset.range 98, ap i) = 137 →
--     ∑ k in Finset.filter (λ n => n % 2 = 0) (Finset.range 99), ap k = 93 := sorry

-- theorem sum_of_coordinates_at_intersection : ∃ (x y : ℝ), 3 * y = x ∧ 2 * x + 5 * y = 11 ∧ x + y = 4 := sorry

-- theorem prime_divides_a_pow_p_minus_a (p : ℕ) (hp : Nat.Prime p) (a : ℕ) (ha : a > 0) : p ∣ a ^ p - a := sorry

-- theorem f_negative_case : ∃ (f : ℚ → ℝ) (h1 : ∀ (a b : ℚ), 0 < a → 0 < b → f (a * b) = f a + f b)
--     (h2 : ∀ (p : ℕ), Nat.Prime p → f (p : ℚ) = (p : ℝ)), f (25/11 : ℚ) < 0 ∧
--     (∀ (x : ℚ), x = (17/32 : ℚ) ∨ x = (11/16 : ℚ) ∨ x = (7/9 : ℚ) ∨ x = (7/6 : ℚ) → ¬(f x < 0)) := sorry

-- theorem solve_for_a : ∃ a : ℝ, (Real.sqrt (4 + Real.sqrt (16 + 16 * a))) + (Real.sqrt (1 + Real.sqrt (1 + a))) = 6 ∧ a = 8 := sorry

-- theorem real_inequality (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : a * b + (a - b) ≤ 1 := sorry

-- theorem floor_sum_computation : (Int.floor (10 * ((1 : ℝ) / 3)) + Int.floor (100 * ((1 : ℝ) / 3)) + Int.floor (1000 * ((1 : ℝ) / 3)) + Int.floor (10000 * ((1 : ℝ) / 3))) = 3702 := sorry

-- theorem inequality_for_positive_reals (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) :
--     a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := sorry

-- theorem units_digit_product : (16^17 * 17^18 * 18^19) % 10 = 8 := sorry

-- theorem number_of_solutions_in_interval :
--     let solutions := {x : ℝ | x ∈ Set.Icc (0 : ℝ) π ∧ Real.sin (π/2 * Real.cos x) = Real.cos (π/2 * Real.sin x)} in
--     Fintype.card solutions = 2 := sorry

-- theorem maximum_value_of_function :
--     IsMaxOn (fun (t : ℝ) => ((2 : ℝ) ^ t - 3 * t) * t / ((4 : ℝ) ^ t)) Set.univ ((1 : ℝ)/12) := sorry

-- theorem minimum_value_at_seven : IsMinOn (fun (x : ℝ) => x ^ 2 - 14 * x + 3) Set.univ 7 := sorry

-- theorem imo_2001_problem :
--     let factors := Finset.filter (λ (x : ℕ) ↦ 2001 % x = 0) (Finset.Icc 1 2001) in
--     Finset.max' (Finset.image (λ (t : ℕ × ℕ × ℕ) ↦ t.1 + t.2.1 + t.2.2)
--       (Finset.filter (λ (t : ℕ × ℕ × ℕ) ↦
--         t.1 * t.2.1 * t.2.2 = 2001 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2)
--         (Finset.product factors (Finset.product factors factors))))
--       (by simp) = 671 := sorry

-- theorem tan_two_x_eq_cos_x_over_two_solutions_count :
--     Fintype.card {x : ℝ | x ∈ Set.Icc (0 : ℝ) (2 * π) ∧ Real.tan (2 * x) = Real.cos (x / 2)} = 5 := sorry

-- theorem gcd_lcm_sum_minimum : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ Nat.gcd m n = 8 ∧ Nat.lcm m n = 112 ∧ m + n = 72 := sorry

-- theorem sum_of_final_three_digits_of_5_pow_100 : (5^100 % 1000).digits.sum = 13 := sorry

-- theorem sequence_parity : (Even (D 2021) ∧ Odd (D 2022) ∧ Even (D 2023)) := sorry

-- theorem positive_nat_root_bound (n : ℕ) (hn : n > 0) : (n : ℝ) ^ ((n : ℝ)⁻¹) ≤ 2 - (n : ℝ)⁻¹ := sorry

-- theorem system_solution : ∃ (a b c : ℝ) (h₁ : a > 0) (h₂ : b > 0) (h₃ : c > 0) (h₄ : a * (b + c) = 152) (h₅ : b * (c + a) = 162) (h₆ : c * (a + b) = 170), a * b * c = 720 := sorry

-- theorem remainder_1529_mod_6 : 1529 % 6 = 5 := sorry

-- theorem compute_square_of_ninety_one : 91 ^ 2 = 8281 := sorry

-- theorem log_3_27_eq_3 : Real.logb 3 27 = 3 := sorry

-- theorem solve_for_a : ∃ a : ℝ, (8⁻¹ / 4⁻¹) - a⁻¹ = 1 ∧ a = -2 := sorry

-- theorem complex_equation_solution : ∃ (z : ℂ), (12 : ℂ) * Complex.normSq z = (2 : ℂ) * Complex.normSq (z + 2) + Complex.normSq (z ^ 2 + 1) + (31 : ℂ) ∧ z + 6 / z = (-2 : ℂ) := sorry

-- theorem arithmetic_geometric_means_solution : ∃ (x y : ℝ), (x + y) / 2 = 7 ∧ Real.sqrt (x * y) = Real.sqrt 19 ∧ x ^ 2 + y ^ 2 = 158 := sorry

-- theorem cube_root_equation_implies_cube_identity (r : ℝ) (h : r ^ (1/3 : ℝ) + (1 : ℝ) / r ^ (1/3 : ℝ) = 3) : r ^ 3 + (1 : ℝ) / r ^ 3 = 5778 := sorry

-- theorem exists_unique_initial_value : ∃! (x₁ : ℝ), ∀ n, 0 < x₁ ∧ (fun (x : ℕ → ℝ) => ∀ k, 0 < x k ∧ x k < x (k + 1) ∧ x (k + 1) < 1) (Nat.rec x₁ (λ n x_n => x_n * (x_n + 1 / (n + 1 : ℝ)))) n := sorry

-- theorem greatest_distance_between_sets :
--     let A : Set ℂ := {z | z ^ 3 - 8 = 0}
--     let B : Set ℂ := {z | z ^ 3 - 8 * z ^ 2 - 8 * z + 64 = 0}
--     in sSup {d | ∃ a ∈ A, ∃ b ∈ B, d = Complex.dist a b} = Real.sqrt 84 := sorry

-- theorem divisibility_property (n : ℕ) : 11 ∣ (10^n - (-1 : ℤ)^n) := sorry

-- theorem product_bound (n : ℕ) (a : ℕ → ℝ) (h_nonneg : ∀ i, 0 ≤ a i) (h_sum : ∑ i in Finset.range n, a i = n) :
--     ∏ i in Finset.range n, a i ≤ 1 := sorry

-- theorem log_problem_solution : (Real.log (x / y) / Real.log 2) ^ 2 = 20 := by
--   sorry

-- theorem find_c_value : ∃! c : ℝ, ∀ x : ℝ, c * x ^ 3 - 9 * x + 3 = f x ∧ f 2 = 9 ∧ c = 3 := sorry

-- theorem bernoulli_inequality (x : ℝ) (n : ℕ) (hx : x > -1) : (1 + (n : ℝ) * x) ≤ (1 + x) ^ n := sorry

-- theorem find_mod_value : ∃! n : ℤ, 0 ≤ n ∧ n < (101 : ℤ) ∧ (123456 : ℤ) ≡ n [ZMOD (101 : ℤ)] := by
--   refine ⟨34, ⟨by norm_num, by norm_num, show (123456 : ℤ) ≡ (34 : ℤ) [ZMOD (101 : ℤ)] from ?_⟩, ?_⟩
--   sorry

-- theorem son_age_today : ∃ (son_age : ℕ), son_age = 6 := by
--   refine ⟨6, rfl⟩
--   sorry

-- theorem arithmetic_series_first_term :
--     ∃ (a d : ℚ), (∑ k in Finset.range 5, (a + k * d)) = 70 ∧ (∑ k in Finset.range 10, (a + k * d)) = 210 ∧ a = 42/5 := sorry

-- theorem residue_mod_four : (121 * 122 * 123) % 4 = 2 := sorry

-- theorem sum_mod_four_eq_two : (∑ i in Finset.range 13, i) % 4 = 2 := sorry

-- theorem problem_solution : (3 * (4 : ℝ) - 2) * (4 * (4 : ℝ) + 1) - (3 * (4 : ℝ) - 2) * 4 * (4 : ℝ) + 1 = (11 : ℝ) := sorry

-- theorem sum_of_solutions : (∑ x in {x : ℝ | |2 - x| = 3}, x) = 4 := sorry

-- theorem product_of_real_roots :
--     let f : ℝ → ℝ := λ x => x^2 + 18*x + 30 - 2 * Real.sqrt (x^2 + 18*x + 45) in
--     let roots : Set ℝ := {x | f x = 0} in
--     ∏ x in roots, x = 20 := sorry

-- theorem f_value_at_3 :
--     ∀ (a b : ℝ) (f : ℝ → ℝ), (∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5) → (f (-3) = 2) → (f 3 = 8) := sorry

-- theorem find_a_minus_d : ∃ (a b c d : ℕ),
--     0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
--     a * b * c * d = Nat.factorial 8 ∧
--     a * b + a + b = 524 ∧
--     b * c + b + c = 146 ∧
--     c * d + c + d = 104 ∧
--     a - d = 10 := sorry

-- theorem father_age_base_conversion : (1222 : ℕ) = 53 := sorry

-- theorem remainder_property (n : ℕ) (hn : n > 0) : (3^(2^n) - 1) % (2^(n + 3)) = 2^(n + 2) := sorry

-- theorem arithmetic_sequence_problem : ∃ (a d : ℤ), (a + 6 * d = 30) ∧ (a + 10 * d = 60) ∧ (a + 20 * d = 135) := sorry

-- theorem f_value_at_84 : f 84 = 997 := sorry

-- theorem integer_functional_equation :
--     Set.EqOn (fun f : ℤ → ℤ ↦ ∀ a b : ℤ, f (2 * a) + 2 * f b = f (f (a + b)))
--     {f | f = fun _ ↦ 0 ∨ f = fun x ↦ x} := sorry

-- theorem composition_value : (fun (x : ℝ) => x + 1) ((fun (x : ℝ) => x ^ 2 + 3) (2 : ℝ)) = (8 : ℝ) := sorry

-- theorem ordered_pair_solution : ∃ (a b : ℝ), 3 * a + 2 * b = 5 ∧ a + b = 2 ∧ (a, b) = (1, 1) := sorry

-- theorem prime_sum_product_difference : ∃ (p q : ℕ), Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ 4 < p ∧ p < 18 ∧ 4 < q ∧ q < 18 ∧ p * q - (p + q) = 119 := sorry

-- theorem marbles_game_removal_count : ∃ (removed : ℕ), removed = 6 := sorry

-- theorem f_property : ∃ (f : ℕ → ℕ → ℕ), (∀ x, f x x = x) ∧ (∀ x y, f x y = f y x) ∧ (∀ x y, (x + y) * f x y = y * f x (x + y)) ∧ f 14 52 = 364 := sorry

-- theorem cube_root_computation : ((16 : ℝ) * ((8 : ℝ) ^ ((2 : ℕ) : ℝ) / (3 : ℝ)) ^ ((1 : ℝ) / (3 : ℝ))) ^ ((1 : ℝ) / (3 : ℝ)) = (4 : ℝ) := sorry

-- theorem radical_simplification : ∀ (x : ℝ), Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := sorry

-- theorem jasmines_water_consumption : (1.5 * (10 : ℝ) / 3) = (5 : ℝ) := sorry

-- theorem number_of_solutions :
--     Finset.card (Finset.filter (λ θ : ℝ => 1 - 3 * Real.sin θ + 5 * Real.cos (3 * θ) = 0)
--     (Finset.Icc (0 : ℝ) (2 * π) ∩ {x | 0 < x})) = 6 := sorry

-- theorem log_sqrt_identity : Real.sqrt (Real.logb 2 6 + Real.logb 3 6) = Real.sqrt (Real.logb 2 3) + Real.sqrt (Real.logb 3 2) := sorry

-- theorem power_mean_inequality (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) (hn : 0 < n) : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := sorry

-- theorem find_expression_value (a b x y : ℝ)
--     (h1 : a * x + b * y = 3)
--     (h2 : a * x ^ 2 + b * y ^ 2 = 7)
--     (h3 : a * x ^ 3 + b * y ^ 3 = 16)
--     (h4 : a * x ^ 4 + b * y ^ 4 = 42) :
--     a * x ^ 5 + b * y ^ 5 = 20 := sorry

-- theorem periodic_function_exists (a : ℝ) (ha : a > 0) (f : ℝ → ℝ)
--     (hf : ∀ x : ℝ, f (x + a) = 1/2 + Real.sqrt (f x - (f x)^2)) :
--     ∃ (b : ℝ), b > 0 ∧ ∀ x : ℝ, f (x + b) = f x := sorry

-- theorem units_digit_computation : (29 * 79 + 31 * 81) % 10 = 2 := sorry

-- theorem remainder_194_mod_11 : 194 % 11 = 7 := sorry

-- theorem real_inequalities (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : a + b + c = 2) (h4 : a * b + b * c + c * a = 1) :
--     0 ≤ a ∧ a ≤ 1/3 ∧ 1/3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4/3 := sorry

-- theorem integer_values_in_interval : Finset.card (Finset.Icc (-9 : ℤ) 9) = 19 := sorry

-- theorem problem_solution : ∃ (x y : ℕ) (hsum : x + y = 17402) (hdiv : 10 ∣ x) (hdigit : x / 10 = y), x - y = 14238 := sorry

-- theorem sequence_sum_problem : ∃ (a₁ b₁ : ℝ), (∀ n : ℕ, let (a, b) := Nat.iterate (λ (p : ℝ × ℝ) => (Real.sqrt 3 * p.1 - p.2, Real.sqrt 3 * p.2 + p.1)) n (a₁, b₁) in (a, b) = (a₁, b₁)) ∧ (Nat.iterate (λ (p : ℝ × ℝ) => (Real.sqrt 3 * p.1 - p.2, Real.sqrt 3 * p.2 + p.1)) 99 (a₁, b₁) = (2, 4)) ∧ a₁ + b₁ = 1 / ((2 : ℝ) ^ 98)) := sorry

-- theorem prime_quadratic_sum : ∃ m n k t : ℕ, Nat.Prime m ∧ Nat.Prime n ∧ k > t ∧ t > 0 ∧ k^2 - m * k + n = 0 ∧ t^2 - m * t + n = 0 ∧ m^n + n^m + k^t + t^k = 20 := sorry

-- theorem consecutive_even_integers_product :
--     ∃! n : ℕ, n > 0 ∧ Even n ∧ Even (n - 2) ∧ (n * (n - 2)) = 288 ∧ n = 18 := sorry

-- theorem reciprocal_difference_sum : ∃ (a b : ℝ), 0 < a ∧ 0 < b ∧ a ≠ b ∧ |(a - a⁻¹)| = 1 ∧ |(b - b⁻¹)| = 1 ∧ a + b = Real.sqrt 5 := sorry

-- theorem triangle_inequality_sides (a b c : ℝ) (h1 : a > 0) (h2 : b > 0) (h3 : c > 0)
--     (h4 : a + b > c) (h5 : b + c > a) (h6 : c + a > b) :
--     a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := sorry

-- theorem find_B_value : B = -88 := sorry

-- theorem solve_for_a_plus_b : ∃ (a b : ℝ), a ^ 2 * b ^ 3 = 32/27 ∧ a / (b ^ 3) = 27/4 ∧ a + b = 8/3 := sorry

-- theorem arithmetic_sequence_nth_term :
--     ∃ (x : ℕ) (n : ℕ),
--       (2*x - 3 : ℤ) + (5*x - 11 - (2*x - 3)) = (3*x + 1 : ℤ) - (5*x - 11) ∧
--       (2*x - 3 : ℤ) + (n - 1) * ((5*x - 11) - (2*x - 3)) = (2009 : ℤ) ∧
--       n = 502 := sorry
