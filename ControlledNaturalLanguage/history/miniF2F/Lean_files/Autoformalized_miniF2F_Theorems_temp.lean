
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


theorem odd_integers_condition (a b c d : ℤ) (ha : Odd a) (hb : Odd b) (hc : Odd c) (hd : Odd d) 
    (hlt : 0 < a ∧ a < b ∧ b < c ∧ c < d) (had : a * d = b * c) 
    (hsum1 : ∃ (k : ℤ), a + d = 2 ^ k) (hsum2 : ∃ (m : ℤ), b + c = 2 ^ m) : a = 1 := sorry

theorem inequality_for_absolute_values (a b : ℝ) : |a + b| / (1 + |a + b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := sorry

theorem multiplicative_inverse_modulo : ∃ n : ℕ, n < 1399 ∧ (160 * n) % 1399 = 1 ∧ n = 1058 := sorry

theorem not_prime_of_equation {K L M N : ℕ} (hK : K > 0) (hL : L > 0) (hM : M > 0) (hN : N > 0) 
  (h_order : K > L ∧ L > M ∧ M > N) 
  (h_eq : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) : 
  ¬ Nat.Prime (K * L + M * N) := sorry

theorem inequality_for_positive_reals : ∀ (x y z : ℝ), x > 0 → y > 0 → z > 0 → 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := sorry

theorem congruence_solution : ∃ n : ℕ, n < 47 ∧ 2 * n % 47 = 15 % 47 ∧ n = 31 := sorry

theorem find_modular_inverse : ∃ (b : ℕ), b < 11^2 ∧ (24 * b) % (11^2) = 1 ∧ b = 116 := sorry

theorem sum_of_variables : ∃ (x y z : ℕ), 3*x + y = 17 ∧ 5*y + z = 14 ∧ 3*x + 5*z = 41 ∧ x + y + z = 12 := sorry

theorem f_value : f (f (f (f (f (4))))) = 1 := sorry

theorem problem_statement : ∀ (n : ℕ) (h : n ≥ 9), ∃ (k : ℕ), ((Nat.factorial (n + 2)) - (Nat.factorial (n + 1))) / (Nat.factorial n) = k ^ 2 := sorry

theorem exist_irrational_power_rational : ∃ (a b : ℝ), Irrational a ∧ Irrational b ∧ Rational (a ^ b) := sorry

theorem smallest_k_satisfies_condition : 
    (∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, 0 < n → Nat.Coprime (6 * n + k) (6 * n + 3) ∧ Nat.Coprime (6 * n + k) (6 * n + 2) ∧ Nat.Coprime (6 * n + k) (6 * n + 1)) ∧
    (∀ k' : ℕ, k' < 5 → ¬(0 < k' ∧ ∀ n : ℕ, 0 < n → Nat.Coprime (6 * n + k') (6 * n + 3) ∧ Nat.Coprime (6 * n + k') (6 * n + 2) ∧ Nat.Coprime (6 * n + k') (6 * n + 1))) := sorry

theorem count_even_digit_divisible_by_five : Finset.card (Finset.filter (λ n : ℕ => 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d : ℕ, d ∈ (Nat.digits 10 n) → Even d) ∧ 5 ∣ n) (Finset.Icc 1000 9999)) = 100 := sorry

theorem log_sum_product_eq_21000 : 
    (∑ k in Finset.Icc 1 20, Real.logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ (k ^ 2))) * 
    (∑ k in Finset.Icc 1 100, Real.logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k)) = (21000 : ℝ) := sorry

theorem sum_sqrt_reciprocal_lt_198 : ∑ k in Finset.Icc 2 10000, (1 : ℝ) / Real.sqrt k < 198 := sorry

theorem euler_polynomial_common_factor :
    ∃ n : ℕ, 0 < n ∧ 1 < Nat.gcd (n ^ 2 - n + 41) ((n + 1) ^ 2 - (n + 1) + 41) ∧
    ∀ m : ℕ, 0 < m → m < n → Nat.gcd (m ^ 2 - m + 41) ((m + 1) ^ 2 - (m + 1) + 41) = 1 := sorry

theorem factor_problem : ∃ (A B : ℤ), (10 : ℤ) * x ^ 2 - x - 24 = (A * x - 8) * (B * x + 3) ∧ A * B + B = 12 := sorry

theorem inequality_for_positive_reals (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hle : b ≤ a) : 
    (a + b)/2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := sorry

theorem perfect_square_divisors_count : 
    let factorial_product : ℕ := ∏ i in Finset.Icc 1 9, Nat.factorial i in
    Finset.card (Finset.filter (λ d : ℕ => ∃ k : ℕ, d = k ^ 2) (Nat.divisors factorial_product)) = 672 := sorry

theorem infinitely_many_m : Set.Infinite {m : ℕ | m > 0 ∧ ∃ n : ℕ, n > 0 ∧ m * n ≤ m + n} := sorry

theorem complex_current_calculation : (1 + Complex.I) / (2 - Complex.I) = (1/5 : ℂ) + (3/5 : ℂ) * Complex.I := sorry

theorem problem_statement : ∃ (n : ℕ) (hn : n > 0), 
    (1/2 + 1/3 + 1/7 + 1/(n : ℚ) : ℚ) ∈ Set.range ((↑) : ℤ → ℚ) ∧ 
    (2 ∣ n) ∧ (3 ∣ n) ∧ (6 ∣ n) ∧ (7 ∣ n) ∧ ¬(n > 84) := sorry

theorem remainder_of_5_pow_30_mod_7 : (5 ^ 30) % 7 = 1 := sorry

theorem find_n_gcd_lcm : ∃ n : ℕ, Nat.gcd n 40 = 10 ∧ Nat.lcm n 40 = 280 ∧ n = 70 := sorry

theorem product_equivalence : (2 + 3) * (2^2 + 3^2) * (2^4 + 3^4) * (2^8 + 3^8) * (2^16 + 3^16) * (2^32 + 3^32) * (2^64 + 3^64) = 3^128 - 2^128 := sorry

theorem polynomial_roots_cosine_product :
    ∃ (a b c : ℝ), (∀ (x : ℝ), x^3 + a * x^2 + b * x + c = (x - Real.cos (2 * π / 7)) * (x - Real.cos (4 * π / 7)) * (x - Real.cos (6 * π / 7))) ∧ a * b * c = 1/32 := sorry

theorem arithmetic_progression_sum_even_terms :
    ∃ (a₁ : ℤ), ∀ (d : ℤ), d = 1 → 
    let seq := λ n : ℕ => a₁ + (n : ℤ) * d in
    (∑ k in Finset.range 98, seq (k + 1)) = 137 → 
    (∑ k in Finset.range 49, seq (2 * (k + 1))) = 93 := sorry

theorem sum_of_coordinates_at_intersection : 
    ∃ (A : ℝ × ℝ), (3 * A.2 = A.1) ∧ (2 * A.1 + 5 * A.2 = 11) ∧ (A.1 + A.2 = 4) := sorry

theorem prime_divides_a_pow_p_minus_a (p : ℕ) (hp : Nat.Prime p) (a : ℕ) (ha : a > 0) : p ∣ a ^ p - a := sorry

theorem problem_solution : f (25/11 : ℚ) < 0 := sorry

theorem solve_for_a : ∃ a : ℝ, (Real.sqrt (4 + Real.sqrt (16 + 16 * a))) + (Real.sqrt (1 + Real.sqrt (1 + a))) = 6 ∧ a = 8 := sorry

theorem real_inequality (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : a * b + (a - b) ≤ 1 := sorry

theorem floor_sum_computation : (Nat.floor (10 * ((1 : ℝ) / 3)) : ℤ) + (Nat.floor (100 * ((1 : ℝ) / 3)) : ℤ) + (Nat.floor (1000 * ((1 : ℝ) / 3)) : ℤ) + (Nat.floor (10000 * ((1 : ℝ) / 3)) : ℤ) = 3702 := sorry

theorem inequality_for_positive_reals (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := sorry

theorem units_digit_product : (Nat.digits 10 (16^17 * 17^18 * 18^19)).head? = some 8 := sorry

theorem number_of_solutions_in_interval : 
    let solutions : Set ℝ := {x | x ∈ Set.Icc (0 : ℝ) π ∧ Real.sin (π/2 * Real.cos x) = Real.cos (π/2 * Real.sin x)}
    in Finset.card (solutions.toFinite.toFinset) = 2 := sorry

theorem maximum_value_of_expression : 
    IsGreatest {x : ℝ | ∃ (t : ℝ), x = ((2^t - 3*t)*t)/(4^t)} (1/12) := sorry

theorem minimum_value_at_seven : IsMinOn (fun (x : ℝ) => x ^ 2 - 14 * x + 3) Set.univ 7 := sorry

theorem imo_2001_problem : 
    let factors := Finset.filter (λ (x : ℕ) ↦ 2001 % x = 0) (Finset.Icc 1 2001) in
    let triples := Finset.filter (λ (t : ℕ × ℕ × ℕ) ↦ 
      let (I, M, O) := t in
      I * M * O = 2001 ∧ I ≠ M ∧ M ≠ O ∧ I ≠ O ∧ I > 0 ∧ M > 0 ∧ O > 0) 
      ((factors : Finset ℕ) ×ˢ (factors : Finset ℕ) ×ˢ (factors : Finset ℕ)) in
    Finset.sup' triples (Finset.Nonempty_of_mem ?_) (λ (t : ℕ × ℕ × ℕ) ↦ 
      let (I, M, O) := t in I + M + O) = 671 := sorry

theorem tan_two_x_eq_cos_x_over_two_solutions_count : 
    Finset.card (Finset.filter (λ x : ℝ => tan (2 * x) = cos (x / 2)) (Finset.Icc (0 : ℝ) (2 * π))) = 5 := sorry

theorem gcd_lcm_sum_minimum : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ Nat.gcd m n = 8 ∧ Nat.lcm m n = 112 ∧ m + n = 72 ∧ ∀ x y : ℕ, 0 < x → 0 < y → Nat.gcd x y = 8 → Nat.lcm x y = 112 → 72 ≤ x + y := sorry

theorem sum_of_final_three_digits_of_5_pow_100 : (Nat.digits 10 (5^100)).reverse.take 3 |>.sum = 13 := sorry

theorem sequence_parity : (Even (D 2021) ∧ Odd (D 2022) ∧ Even (D 2023)) := sorry

theorem positive_nat_root_bound (n : ℕ) (hn : n > 0) : (n : ℝ) ^ ((1 : ℝ) / (n : ℝ)) ≤ 2 - (1 : ℝ) / (n : ℝ) := sorry

theorem product_abc_is_720 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a * (b + c) = 152) (h2 : b * (c + a) = 162) (h3 : c * (a + b) = 170) :
    a * b * c = 720 := sorry

theorem remainder_of_1529_mod_6 : 1529 % 6 = 5 := sorry

theorem compute_square : (91 : ℕ) ^ 2 = 8281 := sorry

theorem log_327_eq_3 : Real.logb 3 27 = 3 := sorry

theorem solve_for_a : ∃ a : ℚ, (8⁻¹ / 4⁻¹) - a⁻¹ = 1 ∧ a = -2 := sorry

theorem complex_problem : ∃ (z : ℂ), (12 : ℂ) * Complex.normSq z = (2 : ℂ) * Complex.normSq (z + (2 : ℂ)) + Complex.normSq (z ^ 2 + (1 : ℂ)) + (31 : ℂ) ∧ z + (6 : ℂ) / z = (-2 : ℂ) := sorry

theorem arithmetic_geometric_means_problem : ∃ (x y : ℝ), (x + y) / 2 = 7 ∧ Real.sqrt (x * y) = Real.sqrt 19 ∧ x ^ 2 + y ^ 2 = 158 := sorry

theorem cube_root_equation_implies_cube_identity (r : ℝ) (h : r ^ (1/3 : ℝ) + (1 : ℝ) / r ^ (1/3 : ℝ) = 3) : r ^ 3 + (1 : ℝ) / r ^ 3 = 5778 := sorry

theorem exists_unique_initial_value : ∃! (x₁ : ℝ), ∀ n, 0 < x₁ ∧ (fun (x : ℕ → ℝ) => ∀ k : ℕ, x (k + 1) = x k * (x k + (1 : ℝ)/(k + 1))) (λ k => Nat.rec x₁ (λ n x_n => x_n * (x_n + (1 : ℝ)/(n + 1))) k) n ∧ (fun (x : ℕ → ℝ) => ∀ k : ℕ, x (k + 1) = x k * (x k + (1 : ℝ)/(k + 1))) (λ k => Nat.rec x₁ (λ n x_n => x_n * (x_n + (1 : ℝ)/(n + 1))) k) (n + 1) ∧ (fun (x : ℕ → ℝ) => ∀ k : ℕ, x (k + 1) = x k * (x k + (1 : ℝ)/(k + 1))) (λ k => Nat.rec x₁ (λ n x_n => x_n * (x_n + (1 : ℝ)/(n + 1))) k) n < (fun (x : ℕ → ℝ) => ∀ k : ℕ, x (k + 1) = x k * (x k + (1 : ℝ)/(k + 1))) (λ k => Nat.rec x₁ (λ n x_n => x_n * (x_n + (1 : ℝ)/(n + 1))) k) (n + 1) ∧ (fun (x : ℕ → ℝ) => ∀ k : ℕ, x (k + 1) = x k * (x k + (1 : ℝ)/(k + 1))) (λ k => Nat.rec x₁ (λ n x_n => x_n * (x_n + (1 : ℝ)/(n + 1))) k) (n + 1) < 1 := sorry

theorem greatest_distance_between_sets :
    let A : Set ℂ := {z | z ^ 3 - 8 = 0}
    let B : Set ℂ := {z | z ^ 3 - 8 * z ^ 2 - 8 * z + 64 = 0}
    sSup {d | ∃ a ∈ A, ∃ b ∈ B, d = Complex.dist a b} = 2 * Real.sqrt 21 := sorry

theorem divisibility_property (n : ℕ) : 11 ∣ (10 : ℤ) ^ n - (-1 : ℤ) ^ n := sorry

theorem product_bound (n : ℕ) (a : ℕ → ℝ) (h_nonneg : ∀ i, 0 ≤ a i) (h_sum : ∑ i in Finset.range n, a i = n) : 
    ∏ i in Finset.range n, a i ≤ 1 := sorry

theorem log_problem : (Real.logb 2 (x / y)) ^ 2 = 20 := by
  sorry

theorem find_c_value : ∃! c : ℝ, ∀ x : ℝ, f x = c * x ^ 3 - 9 * x + 3 ∧ f 2 = 9 → c = 3 := sorry

theorem bernoulli_inequality (x : ℝ) (n : ℕ) (hx : x > -1) : (1 + (n : ℝ) * x) ≤ (1 + x) ^ n := sorry

theorem find_mod_value : ∃ n : ℤ, 0 ≤ n ∧ n < (101 : ℤ) ∧ (123456 : ℤ) ≡ n [ZMOD (101 : ℤ)] ∧ n = (34 : ℤ) := sorry

theorem son_age_today : ∃ (father_age son_age : ℕ), father_age = 5 * son_age ∧ (father_age - 3) + (son_age - 3) = 30 ∧ son_age = 6 := sorry

theorem arithmetic_series_first_term : 
    ∃ (a d : ℚ), (∑ k in Finset.range 5, (a + k * d)) = 70 ∧ (∑ k in Finset.range 10, (a + k * d)) = 210 ∧ a = 42/5 := sorry

theorem residue_mod_four : (121 * 122 * 123) % 4 = 2 := sorry

theorem sum_mod_four_eq_two : (∑ i in Finset.Icc 1 12, i) % 4 = 2 := sorry

theorem problem_solution : (3 * (4 : ℤ) - 2) * (4 * (4 : ℤ) + 1) - (3 * (4 : ℤ) - 2) * 4 * (4 : ℤ) + 1 = (11 : ℤ) := sorry

theorem sum_of_solutions_eq_four : (∑ x in {x : ℝ | |2 - x| = 3}, x) = 4 := sorry

theorem product_of_real_roots : 
    let equation : ℝ → Prop := λ x => x^2 + 18*x + 30 = 2 * Real.sqrt (x^2 + 18*x + 45)
    in let roots : Set ℝ := {x | equation x}
    in (∃ (r : ℝ), r ∈ roots) → (∏ x in roots.toFinset, x) = 20 := sorry

theorem f_value_at_3 : ∀ (a b : ℝ), (∀ (x : ℝ), f x = a * x ^ 4 - b * x ^ 2 + x + 5) → f (-3) = 2 → f 3 = 8 := sorry

theorem problem_solution : ∃ (a b c d : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0),
    a * b * c * d = Nat.factorial 8 ∧
    a * b + a + b = 524 ∧
    b * c + b + c = 146 ∧
    c * d + c + d = 104 ∧
    a - d = 10 := sorry

theorem father_age_base_conversion : (1222 : ℕ) = 53 := sorry

theorem remainder_property (n : ℕ) (hn : n > 0) : (3^(2^n) - 1) % (2^(n + 3)) = (2^(n + 2)) % (2^(n + 3)) := sorry

theorem arithmetic_sequence_problem : ∃ (a d : ℤ), (a + 6 * d = 30) ∧ (a + 10 * d = 60) ∧ (a + 20 * d = 135) := sorry

theorem f_value_at_84 : f 84 = 997 := sorry

theorem functional_equation_on_integers : 
    ∃ (f : ℤ → ℤ), ∀ (a b : ℤ), f (2 * a) + 2 * f b = f (f (a + b)) := sorry

theorem composition_value : (fun (x : ℝ) => x + 1) ((fun (x : ℝ) => x ^ 2 + 3) (2 : ℝ)) = (8 : ℝ) := sorry

theorem ordered_pair_solution : ∃ (a b : ℤ), 3 * a + 2 * b = 5 ∧ a + b = 2 ∧ (a, b) = (1, 1) := sorry

theorem prime_sum_product_difference : ∃ (p q : ℕ), Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ 4 < p ∧ p < 18 ∧ 4 < q ∧ q < 18 ∧ p * q - (p + q) = 119 := sorry

theorem marbles_removal : (239 + 174 + 83) % 10 = 6 := sorry

theorem f_property : ∀ (x y : ℕ) (hx : x > 0) (hy : y > 0), f x x = x ∧ f x y = f y x ∧ (x + y) * f x y = y * f x (x + y) := sorry

theorem calculate_f_14_52 : f 14 52 = 364 := sorry

theorem cube_root_computation : (16 * (Real.rpow (8 : ℝ) (2/3 : ℝ)) ^ (1/3 : ℝ)) = (4 : ℝ) := sorry

theorem radical_simplification : ∀ (x : ℝ), Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := sorry

theorem jasmines_water_consumption : (1.5 * (10 : ℝ) / 3) = (5 : ℝ) := sorry

theorem count_theta_solutions : Finset.card (Finset.filter (λ θ : ℝ => 1 - 3 * Real.sin θ + 5 * Real.cos (3 * θ) = 0) 
    (Finset.Icc (0 : ℝ) (2 * π) \ {0})) = 6 := sorry

theorem log_sqrt_problem : Real.sqrt (Real.logb 2 6 + Real.logb 3 6) = Real.sqrt (Real.logb 2 3) + Real.sqrt (Real.logb 3 2) := sorry

theorem power_mean_inequality (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) (hn : 0 < n) : ((a + b)/2) ^ n ≤ (a ^ n + b ^ n)/2 := sorry

theorem find_ax5_by5 (a b x y : ℝ) (h1 : a * x + b * y = 3) (h2 : a * x^2 + b * y^2 = 7) 
    (h3 : a * x^3 + b * y^3 = 16) (h4 : a * x^4 + b * y^4 = 42) : a * x^5 + b * y^5 = 20 := sorry

theorem periodic_function_exists (a : ℝ) (ha : a > 0) (f : ℝ → ℝ) 
    (hf : ∀ x : ℝ, f (x + a) = 1/2 + Real.sqrt (f x - (f x)^2)) :
    ∃ (b : ℝ) (hb : b > 0), ∀ x : ℝ, f (x + b) = f x := sorry

theorem units_digit_computation : (29 * 79 + 31 * 81) % 10 = 2 := sorry

theorem remainder_of_194_mod_11 : 194 % 11 = 7 := sorry

theorem real_inequalities (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : a + b + c = 2) (h4 : a * b + b * c + c * a = 1) : 
    0 ≤ a ∧ a ≤ 1/3 ∧ 1/3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4/3 := sorry

theorem integer_values_satisfying_abs_x_lt_3pi : Finset.card (Finset.Icc (-⌊3 * π⌋) (⌊3 * π⌋) : Finset ℤ) = 19 := sorry

theorem problem_solution : ∃ (a b : ℕ) (hsum : a + b = 17402) (hdiv : 10 ∣ a) (herase : a / 10 = b), a - b = 14238 := sorry

theorem problem_solution : ∃ (a₁ b₁ : ℝ), (∀ n : ℕ, let (a, b) := Nat.iterate (λ (p : ℝ × ℝ) => (Real.sqrt 3 * p.1 - p.2, Real.sqrt 3 * p.2 + p.1)) n (a₁, b₁) in a = p.1 ∧ b = p.2) ∧ (Nat.iterate (λ (p : ℝ × ℝ) => (Real.sqrt 3 * p.1 - p.2, Real.sqrt 3 * p.2 + p.1)) 99 (a₁, b₁) = (2, 4)) ∧ a₁ + b₁ = 1 / ((2 : ℝ) ^ (98 : ℕ))) := sorry

theorem prime_quadratic_sum : ∃ (m n k t : ℕ), Nat.Prime m ∧ Nat.Prime n ∧ k > t ∧ t > 0 ∧ k^2 - m * k + n = 0 ∧ t^2 - m * t + n = 0 ∧ m^n + n^m + k^t + t^k = 20 := sorry

theorem consecutive_even_product_greater : ∃ (n : ℕ), (2 * n) * (2 * n + 2) = 288 ∧ 2 * n + 2 = 18 := sorry

theorem reciprocal_difference_sum : ∃ (a b : ℝ), 0 < a ∧ 0 < b ∧ a ≠ b ∧ |(a - (1 : ℝ)/a)| = 1 ∧ |(b - (1 : ℝ)/b)| = 1 ∧ a + b = Real.sqrt 5 := sorry

theorem triangle_inequality_sides (a b c : ℝ) (h1 : a + b > c) (h2 : b + c > a) (h3 : c + a > b) (h4 : a > 0) (h5 : b > 0) (h6 : c > 0) : a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := sorry

theorem problem_solution : B = -88 := sorry

theorem solve_for_a_plus_b : ∃ (a b : ℝ), a ^ 2 * b ^ 3 = 32/27 ∧ a / b ^ 3 = 27/4 ∧ a + b = 8/3 := sorry

theorem arithmetic_sequence_nth_term :
    ∃ (x : ℤ) (d : ℤ) (n : ℕ),
      (2*x - 3) + d = 5*x - 11 ∧
      (5*x - 11) + d = 3*x + 1 ∧
      (2*x - 3) + (n : ℤ) * d = 2009 ∧
      n = 502 := sorry

