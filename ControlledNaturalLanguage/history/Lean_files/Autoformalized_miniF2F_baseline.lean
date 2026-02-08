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
(h₁ : 0 < a) (h₂ : a < b) (h₃ : b < c) (h₄ : c < d) (h₅ : a * d = b * c) 
(k m : ℕ) (h₆ : a + d = 2 ^ k) (h₇ : b + c = 2 ^ m) : a = 1 := sorry

theorem abs_add_div_one_plus_abs_add_le_abs_div_one_plus_abs_add_abs_div_one_plus_abs (a b : ℝ) : |a + b| / (1 + |a + b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := sorry

theorem find_inverse : ∃ n : ℤ, 0 ≤ n ∧ n < 1399 ∧ (160 * n) % 1399 = 1 ∧ n = 1058 := sorry

theorem KL_MN_not_prime (K L M N : ℕ) (hK : K > 0) (hL : L > 0) (hM : M > 0) (hN : N > 0) (h_ineq : K > L ∧ L > M ∧ M > N) (h_eq : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) : ¬ Nat.Prime (K * L + M * N) := sorry

theorem inequality_for_three_pos_reals (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := sorry

theorem solve_congruence : ∃! n : Fin 47, (2 * ↑n) % 47 = 15 % 47 ∧ ↑n = 31 := sorry

theorem find_modular_inverse : ∃! b, b < 11^2 ∧ 24 * b ≡ 1 [MOD 11^2] ∧ b = 116 := sorry

theorem solve_system : ∀ (x y z : ℝ), 3 * x + y = 17 → 5 * y + z = 14 → 3 * x + 5 * z = 41 → x + y + z = 12 := sorry

theorem f_f_f_f_f_4_eq_1 : let f : ℤ → ℤ := fun n => if Int.Odd n then n ^ 2 else n ^ 2 - 4 * n - 1; f (f (f (f (f 4)))) = 1 := sorry

theorem factorial_ratio_perfect_square (n : ℤ) (hn : n ≥ 9) : ∃ k : ℤ, ((Nat.factorial (n + 2) - Nat.factorial (n + 1)) / Nat.factorial n) = k ^ 2 := sorry

theorem exists_irrational_pow_irrational_rational : ∃ (a b : ℝ), Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := sorry

theorem smallest_k : IsLeast {k | 0 < k ∧ ∀ n, Nat.coprime (6*n + k) (6*n + 3) ∧ Nat.coprime (6*n + k) (6*n + 2) ∧ Nat.coprime (6*n + k) (6*n + 1)} 5 := sorry

theorem count_4digit_even_digits_divisible_by_5 : 
  Finset.card (Finset.filter (fun n => (1000 ≤ n ∧ n ≤ 9999) ∧ (∀ d ∈ Nat.digits 10 n, Even d) ∧ n % 5 = 0) Finset.univ) = 100 := sorry

theorem log_sum_problem : 
  (∑ k in Finset.Icc 1 20, Real.log (3^(k^2)) / Real.log (5^k)) * 
  (∑ k in Finset.Icc 1 100, Real.log (25^k) / Real.log (9^k)) = 21000 := sorry

theorem sum_recip_sqrt_lt : ∑ k in Finset.Icc 2 10000, (1 / Real.sqrt ↑k) < 198 := sorry

theorem euler_poly_shared_factor : 
  ∃ n : ℕ, 0 < n ∧ Nat.gcd (n^2 - n + 41) ((n+1)^2 - (n+1) + 41) > 1 ∧ 
  ∀ m : ℕ, 0 < m → m < n → Nat.gcd (m^2 - m + 41) ((m+1)^2 - (m+1) + 41) = 1 := sorry

theorem problem_solution (A B : ℤ) (h : 10 * x^2 - x - 24 = (A * x - 8) * (B * x + 3)) : A * B + B = 12 := sorry

theorem inequality_for_positive_reals (a b : ℝ) (ha : a > 0) (hb : b > 0) (hle : b ≤ a) : (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := sorry

theorem perfect_square_divisors_of_factorial_product : Fintype.card {d : ℕ | ∃ k : ℕ, d = k^2 ∧ d ∣ (∏ i in Finset.Icc 1 9, Nat.factorial i)} = 672 := sorry

theorem count_m_with_n_exists : {m : ℕ | m > 0 ∧ ∃ n : ℕ, n > 0 ∧ m * n ≤ m + n}.Infinite := sorry

theorem complex_current_calculation : ∃ I : ℂ, (1 + Complex.I) = I * (2 - Complex.I) ∧ I = (1 / 5 : ℂ) + (3 / 5 : ℂ) * Complex.I := sorry

theorem problem_statement (n : ℕ) (hn : n > 0) (h : (1/2 + 1/3 + 1/7 + 1/(↑n : ℚ)) ∈ ℤ) : ¬(2 ∣ n ∧ 3 ∣ n ∧ 6 ∣ n ∧ 7 ∣ n ∧ n > 84) := sorry

theorem remainder_5_pow_30_mod_7 : 5 ^ 30 % 7 = 1 := sorry

theorem find_n (n : ℕ) (h₁ : Nat.gcd n 40 = 10) (h₂ : Nat.lcm n 40 = 280) : n = 70 := sorry

theorem product_equivalence : (2 + 3) * (2^2 + 3^2) * (2^4 + 3^4) * (2^8 + 3^8) * (2^16 + 3^16) * (2^32 + 3^32) * (2^64 + 3^64) = 3^128 - 2^128 := sorry

theorem polynomial_roots_cos_2pi_7 : ∃ (a b c : ℝ), (∀ x, x^3 + a * x^2 + b * x + c = (x - Real.cos (2 * π / 7)) * (x - Real.cos (4 * π / 7)) * (x - Real.cos (6 * π / 7))) ∧ a * b * c = 1 / 32 := sorry

theorem sum_even_terms_in_arithmetic_progression (a₁ : ℚ) : 
    let d := (1 : ℚ)
    let n := 49
    let S_total := (98 : ℚ) / 2 * (2 * a₁ + (98 - 1) * d)
    let S_even := n * (a₁ + d + a₁ + (2 * n - 1) * d) / 2
    S_total = 137 → S_even = 93 := sorry

theorem sum_of_coordinates_at_intersection : ∃ (A : ℝ × ℝ), (3 * A.2 = A.1) ∧ (2 * A.1 + 5 * A.2 = 11) ∧ (A.1 + A.2 = 4) := sorry

theorem prime_divides_a_pow_p_sub_a (p : ℕ) (hp : Nat.Prime p) (a : ℕ) (ha : a > 0) : p ∣ (a^p - a) := sorry

theorem problem_solution (f : ℚ → ℚ) (hf_mul : ∀ a b : ℚ, 0 < a → 0 < b → f (a * b) = f a + f b) (hf_prime : ∀ p : ℕ, Nat.Prime p → f p = p) : f (25 / 11) < 0 ∧ (∀ x ∈ {(17 / 32 : ℚ), 11 / 16, 7 / 9, 7 / 6}, ¬(f x < 0)) := sorry

theorem solve_for_a : ∃! a : ℝ, Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 ∧ a = 8 := sorry

theorem real_inequality (a b : ℝ) (h : a^2 + b^2 = 1) : a * b + (a - b) ≤ 1 := sorry

theorem floor_sum_calculation : Int.floor (10 * (1/3 : ℝ)) + Int.floor (100 * (1/3 : ℝ)) + Int.floor (1000 * (1/3 : ℝ)) + Int.floor (10000 * (1/3 : ℝ)) = 3702 := sorry

theorem inequality_of_positive_reals (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := sorry

theorem units_digit_product : (16^17 * 17^18 * 18^19) % 10 = 8 := sorry

theorem count_solutions_in_interval : Finset.card (Finset.filter (fun x => sin (π/2 * Real.cos x) = Real.cos (π/2 * Real.sin x)) (Finset.Icc 0 π)) = 2 := sorry

theorem max_value_problem : IsGreatest {x : ℝ | ∃ (t : ℝ), x = (2^t - 3 * t) * t / 4^t} (1 / 12) := sorry

theorem min_quadratic_value : IsLeast {x : ℝ | ∀ y, x^2 - 14 * x + 3 ≤ y^2 - 14 * y + 3} 7 := sorry

theorem imo_2001_problem : 
  ∀ (I M O : ℕ), I ≠ M → M ≠ O → O ≠ I → I > 0 → M > 0 → O > 0 → I * M * O = 2001 → 
  I + M + O ≤ 671 := sorry

theorem tan_2x_eq_cos_x_over_2_solutions : Fintype.card {x : ℝ | x ∈ Set.Icc 0 (2 * Real.pi) ∧ Real.tan (2 * x) = Real.cos (x / 2)} = 5 := sorry

theorem gcd_lcm_condition (m n : ℕ) (hm : m > 0) (hn : n > 0) (hgcd : Nat.gcd m n = 8) (hlcm : Nat.lcm m n = 112) : m + n ≥ 72 ∧ ∃ m' n', m' + n' = 72 ∧ Nat.gcd m' n' = 8 ∧ Nat.lcm m' n' = 112 := sorry

theorem sum_last_three_digits_of_5_pow_100 : (5^100 % 1000 / 100) + (5^100 % 100 / 10) + (5^100 % 10) = 13 := sorry

theorem D_parity : ∀ n ≥ 3, (D n ≡ D (n - 1) + D (n - 3) [MOD 2]) ∧ (D 0 ≡ 0 [MOD 2]) ∧ (D 1 ≡ 0 [MOD 2]) ∧ (D 2 ≡ 1 [MOD 2]) → (D 2021 ≡ 0 [MOD 2] ∧ D 2022 ≡ 1 [MOD 2] ∧ D 2023 ≡ 0 [MOD 2]) := sorry

theorem pow_n_root_le_two_minus_inv (n : ℕ) (hn : n > 0) : (n : ℝ) ^ (1 / (n : ℝ)) ≤ 2 - (1 / (n : ℝ)) := sorry

theorem abc_product (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h1 : a * (b + c) = 152) (h2 : b * (c + a) = 162) (h3 : c * (a + b) = 170) : a * b * c = 720 := sorry

theorem remainder_1529_mod_6 : 1529 % 6 = 5 := sorry

theorem compute_91_squared : 91 ^ 2 = 8281 := sorry

theorem log_base_3_27_eq_3 : Real.logb 3 27 = 3 := sorry

theorem solve_for_a : ∃ a : ℚ, (8⁻¹ / 4⁻¹) - a⁻¹ = 1 ∧ a = -2 := sorry

theorem complex_number_problem (z : ℂ) (h : 12 * Complex.normSq z = 2 * Complex.normSq (z + 2) + Complex.normSq (z^2 + 1) + 31) : z + 6 / z = -2 := sorry

theorem real_numbers_with_means (x y : ℝ) (h₁ : (x + y) / 2 = 7) (h₂ : Real.sqrt (x * y) = Real.sqrt 19) : x^2 + y^2 = 158 := sorry

theorem cube_root_condition_implies_cube_equation (r : ℝ) (h : r^(1/3) + (1/r)^(1/3) = 3) : r^3 + (1/r)^3 = 5778 := sorry

theorem unique_initial_value_for_increasing_bounded_sequence : ∃! (x₁ : ℝ), ∀ (n : ℕ), 0 < x₁ ∧ x₁ < 1 ∧ ∀ (k : ℕ), k ≥ 1 → let xₖ₊₁ := xₖ * (xₖ + 1/↑k) in 0 < xₖ ∧ xₖ < xₖ₊₁ ∧ xₖ₊₁ < 1 := sorry

theorem greatest_distance_between_solution_sets : 
  let A := {z : ℂ | z^3 - 8 = 0}, 
      B := {z : ℂ | z^3 - 8*z^2 - 8*z + 64 = 0} in 
  sSup {d | ∃ a ∈ A, ∃ b ∈ B, d = Complex.abs (a - b)} = 2 * Real.sqrt 21 := sorry

theorem eleven_divides_pow_ten_plus_minus_one (n : ℕ) : 11 ∣ (10 ^ n - (-1) ^ n) := sorry

theorem prod_le_one_of_sum_eq_n (n : ℕ) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i in Finset.range n, a i = n) : ∏ i in Finset.range n, a i ≤ 1 := sorry

theorem log_problem (x y : ℝ) (hx_pos : x > 0) (hy_pos : y > 0) (hx_ne1 : x ≠ 1) (hy_ne1 : y ≠ 1) (h_log : Real.logb 2 x = Real.logb y 16) (h_xy : x * y = 64) : (Real.logb 2 (x / y))^2 = 20 := sorry

theorem find_coefficient_c (f : ℝ → ℝ) (c : ℝ) (h : ∀ x, f x = c * x^3 - 9 * x + 3) (h2 : f 2 = 9) : c = 3 := sorry

theorem bernoulli_inequality (x : ℝ) (n : ℕ) (hx : x > -1) : (1 + n * x) ≤ (1 + x) ^ n := sorry

theorem find_mod_value : ∃! (n : ℤ), 0 ≤ n ∧ n < 101 ∧ 123456 ≡ n [ZMOD 101] ∧ n = 34 := sorry

theorem son_age_today : ∃ (son_age : ℕ), son_age = 6 ∧ ∃ (father_age : ℕ), father_age = 5 * son_age ∧ father_age - 3 + (son_age - 3) = 30 := sorry

theorem arithmetic_series_first_term (a d : ℚ) : (∑ k in Finset.range 5, a + k * d) = 70 → (∑ k in Finset.range 10, a + k * d) = 210 → a = 42/5 := sorry

theorem residue_121_122_123_mod4 : (121 * 122 * 123) % 4 = 2 := sorry

theorem sum_mod_four : (1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10 + 11 + 12) % 4 = 2 := sorry

theorem problem_value_at_x_4 : (3 * 4 - 2) * (4 * 4 + 1) - (3 * 4 - 2) * 4 * 4 + 1 = 11 := sorry

theorem sum_of_solutions_abs_eq : ∑ x in {x : ℝ | |2 - x| = 3}.toFinset, x = 4 := sorry

theorem product_of_real_roots : (∃ (x : ℝ), x^2 + 18 * x + 30 = 2 * Real.sqrt (x^2 + 18 * x + 45)) → (∃ (a b : ℝ), (∀ (x : ℝ), x^2 + 18 * x + 30 = 2 * Real.sqrt (x^2 + 18 * x + 45) ↔ x = a ∨ x = b) ∧ a * b = 20) := sorry

theorem f_value_at_3 (a b : ℝ) (f : ℝ → ℝ) (h : ∀ x, f x = a * x^4 - b * x^2 + x + 5) (h_neg3 : f (-3) = 2) : f 3 = 8 := sorry

theorem four_integers_product_8factorial (a b c d : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (hprod : a * b * c * d = Nat.factorial 8) (h1 : a * b + a + b = 524) (h2 : b * c + b + c = 146) (h3 : c * d + c + d = 104) : a - d = 10 := sorry

theorem fathers_age_base_conversion : (Nat.ofDigits 3 [1, 2, 2, 2] : ℕ) = 53 := sorry

theorem remainder_congruence (n : ℕ) (hn : n > 0) : (3^(2^n) - 1) ≡ 2^(n+2) [MOD 2^(n+3)] := sorry

theorem arithmetic_sequence_terms (a d : ℚ) (h7 : a + 6 * d = 30) (h11 : a + 10 * d = 60) : a + 20 * d = 135 := sorry

theorem f_84_eq_997 : ∃ f : ℤ → ℤ, (∀ n ≥ 1000, f n = n - 3) ∧ (∀ n < 1000, f n = f (f (n + 5))) ∧ f 84 = 997 := sorry

theorem functional_equation : ∀ f : ℤ → ℤ, (∀ a b : ℤ, f (2 * a) + 2 * f b = f (f (a + b))) → ∃ c : ℤ, ∀ x : ℤ, f x = c ∨ f x = 2 * x + c := sorry

theorem composition_value : let f := fun x : ℝ => x + 1; let g := fun x : ℝ => x^2 + 3; f (g 2) = 8 := sorry

theorem solve_system : ∃ (a b : ℝ), 3 * a + 2 * b = 5 ∧ a + b = 2 ∧ a = 1 ∧ b = 1 := sorry

theorem prime_pair_property : ∃ (p q : ℕ), Nat.Prime p ∧ Nat.Prime q ∧ 4 < p ∧ p < 18 ∧ 4 < q ∧ q < 18 ∧ p ≠ q ∧ p * q - (p + q) = 119 := sorry

theorem marbles_to_remove : (239 + 174 + 83) % 10 = 6 := sorry

theorem f_properties (f : ℕ × ℕ → ℕ) (h₁ : ∀ x, f (x, x) = x) (h₂ : ∀ x y, f (x, y) = f (y, x)) (h₃ : ∀ x y, (x + y) * f (x, y) = y * f (x, x + y)) : f (14, 52) = 364 := sorry

theorem cube_root_calculation : (16 * (8 : ℝ)^(2/3))^(1/3) = 4 := sorry

theorem sqrt_product (x : ℝ) (hx : x ≥ 0) : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := sorry

theorem jasmine_water_consumption : ∃ rate : ℚ, rate = 1.5 / 3 ∧ rate * 10 = 5 := sorry

theorem count_theta_values : Fintype.card {θ : ℝ | θ ∈ Set.Ioc 0 (2 * π) ∧ 1 - 3 * Real.sin θ + 5 * Real.cos (3 * θ) = 0} = 6 := sorry

theorem log_sqrt_identity : Real.sqrt (Real.logb 2 6 + Real.logb 3 6) = Real.sqrt (Real.logb 2 3) + Real.sqrt (Real.logb 3 2) := sorry

theorem power_mean_inequality (a b : ℝ) (ha : a > 0) (hb : b > 0) (n : ℕ) (hn : n > 0) : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := sorry

theorem find_ax5_by5 (a b x y : ℝ) (h1 : a * x + b * y = 3) (h2 : a * x^2 + b * y^2 = 7) (h3 : a * x^3 + b * y^3 = 16) (h4 : a * x^4 + b * y^4 = 42) : a * x^5 + b * y^5 = 20 := sorry

theorem periodic_function_exists (a : ℝ) (ha : a > 0) (f : ℝ → ℝ) (hf : ∀ x, f (x + a) = 1/2 + Real.sqrt (f x - f x ^ 2)) : ∃ b > 0, ∀ x, f (x + b) = f x := sorry

theorem units_digit_calculation : (Nat.mod (29 * 79 + 31 * 81) 10) = 2 := sorry

theorem remainder_194_mod_11 : 194 % 11 = 7 := sorry

theorem real_numbers_bounds (a b c : ℝ) (hle : a ≤ b ∧ b ≤ c) (hsum : a + b + c = 2) (hprod : a * b + b * c + c * a = 1) : 0 ≤ a ∧ a ≤ 1 / 3 ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := sorry

theorem count_integer_values_in_abs_lt_three_pi : Finset.card (Finset.Icc (-⌊3 * π⌋) ⌊3 * π⌋) = 19 := sorry

theorem sum_and_difference_problem : ∃ (a b : ℕ), a + b = 17402 ∧ (10 ∣ a ∨ 10 ∣ b) ∧ (a / 10 = b ∨ b / 10 = a) ∧ |a - b| = 14238 := sorry

theorem sequence_problem (a b : ℕ → ℝ) (h : ∀ n, (a (n + 1), b (n + 1)) = (Real.sqrt 3 * a n - b n, Real.sqrt 3 * b n + a n)) (h100 : (a 100, b 100) = (2, 4)) : a 1 + b 1 = (1 : ℝ) / 2^98 := sorry

theorem prime_roots_sum (m n k t : ℕ) (hp_m : Nat.Prime m) (hp_n : Nat.Prime n) 
  (h_roots : k * t = n ∧ k + t = m) (h_ord : k > t) (h_pos : k > 0 ∧ t > 0) : 
  m ^ n + n ^ m + k ^ t + t ^ k = 20 := sorry

theorem consecutive_even_product (n : ℕ) (h₁ : Nat.Even n) (h₂ : n > 0) (h₃ : n * (n + 2) = 288) : n + 2 = 18 := sorry

theorem sum_of_reciprocal_difference_numbers : ∃ (a b : ℝ), a ≠ b ∧ a > 0 ∧ b > 0 ∧ a - (1 / a) = 1 ∧ b - (1 / b) = 1 ∧ a + b = Real.sqrt 5 := sorry

theorem triangle_inequality (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h₁ : a + b > c) (h₂ : b + c > a) (h₃ : c + a > b) : a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := sorry

theorem problem_solution (A B C D : ℤ) (f : ℤ[X]) (hf : f = Polynomial.monomial 6 1 - Polynomial.monomial 5 10 + Polynomial.monomial 4 A + Polynomial.monomial 3 B + Polynomial.monomial 2 C + Polynomial.monomial 1 D + Polynomial.monomial 0 16) (hroots : ∀ z : ℤ, Polynomial.IsRoot f z → z > 0) : B = -88 := sorry

theorem solve_for_a_b (a b : ℝ) (h1 : a^2 * b^3 = 32 / 27) (h2 : a / b^3 = 27 / 4) : a + b = 8 / 3 := sorry

theorem arithmetic_sequence_nth_term (x n : ℕ) (h₁ : 2 * (5 * x - 11) = (2 * x - 3) + (3 * x + 1)) (h₂ : ∃ d : ℤ, (5 * x - 11) = (2 * x - 3) + d ∧ (3 * x + 1) = (5 * x - 11) + d) (h₃ : ∃ a d : ℤ, 2009 = a + (n - 1) * d ∧ a = 2 * x - 3 ∧ ∃ (h : ℤ), d = h) : n = 502 := sorry

