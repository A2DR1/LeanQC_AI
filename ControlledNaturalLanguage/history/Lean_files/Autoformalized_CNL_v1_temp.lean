
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
    (hsum1 : ∃ k : ℤ, a + d = 2 ^ k) (hsum2 : ∃ m : ℤ, b + c = 2 ^ m) : a = 1 := sorry

theorem f_inequality : ∀ (a b : ℝ), f (|a + b|) ≤ f (|a|) + f (|b|) := sorry

theorem multiplicative_inverse_verification : ∃ n : ℤ, 0 ≤ n ∧ n < 1399 ∧ (160 * n) % 1399 = 1 ∧ n = 1058 := sorry

theorem not_prime_of_condition (K L M N : ℕ) (hK : K > L) (hL : L > M) (hM : M > N) (hpos : N > 0) 
    (h : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) : ¬ Nat.Prime (K * L + M * N) := sorry

theorem three_positive_reals_inequality : ∃ (x y z : ℝ), x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z > 0 ∧ 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := sorry

theorem congruence_solution : ∃ n : ℕ, (2 * n) % 47 = 15 % 47 ∧ n % 47 = 31 := sorry

theorem modular_inverse_24_mod_121 : ∃ (b : ℤ), 24 * b ≡ 1 [ZMOD 121] ∧ b = 116 := sorry

theorem system_solution_sum : ∃ (x y z : ℤ), (3 * x + y = 17) ∧ (5 * y + z = 14) ∧ (3 * x + 5 * z = 41) ∧ (x + y + z = 12) := sorry

theorem function_computation : f (f (f (f (f 4)))) = 1 := sorry

theorem perfect_square_expression (n : ℤ) (hn : n ≥ 9) : ∃ (k : ℤ), (n + 2) ^ 2 = k ^ 2 := sorry

theorem irrational_power_rational : ∃ (a b : ℝ), Irrational a ∧ Irrational b ∧ ¬Irrational (a ^ b) := by
  by_cases h : Irrational ((Real.sqrt 2) ^ (Real.sqrt 2))
  · refine ⟨(Real.sqrt 2) ^ (Real.sqrt 2), Real.sqrt 2, h, irrational_sqrt_two, ?_⟩
    rw [show ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = (2 : ℝ) by ?_]
    exact not_irrational_of_rat (by norm_num) (by norm_num)
  · refine ⟨Real.sqrt 2, Real.sqrt 2, irrational_sqrt_two, irrational_sqrt_two, ?_⟩
    exact not_irrational_of_rat (by norm_num) (by norm_num)

theorem smallest_k_satisfies_condition : ∃ k : ℕ, 0 < k ∧ (∀ n : ℕ, 0 < n → 
    Nat.Coprime (6 * n + k) (6 * n + 3) ∧ 
    Nat.Coprime (6 * n + k) (6 * n + 2) ∧ 
    Nat.Coprime (6 * n + k) (6 * n + 1)) ∧
    ∀ m : ℕ, 0 < m → m < k → ¬(∀ n : ℕ, 0 < n → 
    Nat.Coprime (6 * n + m) (6 * n + 3) ∧ 
    Nat.Coprime (6 * n + m) (6 * n + 2) ∧ 
    Nat.Coprime (6 * n + m) (6 * n + 1)) := sorry

theorem four_digit_even_divisible_by_5_count : 
    Finset.card (Finset.filter (λ n : ℕ ↦ n ≥ 1000 ∧ n ≤ 9999 ∧ (∀ d : ℕ, d ∈ Nat.digits 10 n → Even d) ∧ n % 5 = 0) (Finset.Icc 1000 9999)) = 100 := sorry

theorem expression_evaluation : 
    (∑ k in Finset.Icc 1 20, Real.logb ((5 : ℝ) ^ k) ((3 : ℝ) ^ (k ^ 2))) * 
    (∑ k in Finset.Icc 1 100, Real.logb ((9 : ℝ) ^ k) ((25 : ℝ) ^ k)) = (21000 : ℝ) := sorry

theorem sum_reciprocal_sqrt_lt_198 : ∑ k in Finset.Icc 2 10000, 1 / Real.sqrt k < 198 := sorry

theorem euler_polynomial_common_factor :
    let p (n : ℕ) : ℕ := n ^ 2 - n + 41 in
    ∃ n : ℕ, 0 < n ∧ 1 < Nat.gcd (p n) (p (n + 1)) ∧
    ∀ m : ℕ, 0 < m → m < n → ¬(1 < Nat.gcd (p m) (p (m + 1))) := sorry

theorem solve_expression : ∃ (A B : ℤ), (10 : ℤ) * x ^ 2 - x - 24 = (A * x - 8) * (B * x + 3) ∧ A * B = 10 ∧ 3 * A - 8 * B = -1 ∧ A = 5 ∧ B = 2 ∧ A * B + B = 12 := sorry

theorem inequality_statement (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hle : b ≤ a) : (a + b)/2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := sorry

theorem perfect_square_divisors_count : 
    let product := ∏ n : ℕ in Finset.Icc 1 9, Nat.factorial n in
    let prime_factors := {2, 3, 5, 7} in
    let exponents : ℕ → ℕ := λ p => if p = 2 then 30 else if p = 3 then 13 else if p = 5 then 5 else if p = 7 then 2 else 0 in
    let choices : ℕ → ℕ := λ p => if p = 2 then 16 else if p = 3 then 7 else if p = 5 then 3 else if p = 7 then 2 else 1 in
    (∏ p in prime_factors, choices p) = 672 := sorry

theorem infinite_m_n_satisfying_inequality : Set.Infinite {m : ℕ | ∃ n : ℕ, 0 < m ∧ 0 < n ∧ m * n ≤ m + n} := sorry

theorem find_current : 
    let V : ℂ := 1 + Complex.I
    let Z : ℂ := 2 - Complex.I
    let I : ℂ := V / Z in
    I = (1/5 : ℂ) + (3/5 : ℂ) * Complex.I := sorry

theorem positive_integer_sum_condition : ∀ (n : ℕ), 0 < n → (1/2 + 1/3 + 1/7 + 1/(n : ℚ) : ℚ) ∈ Set.range ((↑) : ℤ → ℚ) → n ∣ 42 ∧ n ≤ 84 := sorry

theorem remainder_of_5_pow_30_mod_7 : (5 : ℤ) ^ 30 % 7 = 1 := sorry

theorem find_n : ∃ n : ℕ, Nat.gcd n 40 = 10 ∧ Nat.lcm n 40 = 280 ∧ n * 40 = (Nat.gcd n 40) * (Nat.lcm n 40) ∧ n * 40 = 10 * 280 ∧ n * 40 = 2800 ∧ n = 2800 / 40 ∧ 2800 / 40 = 70 ∧ n = 70 := sorry

theorem expression_equals_power_difference : (3 : ℕ) ^ 128 - (2 : ℕ) ^ 128 = (3 : ℕ) ^ 128 - (2 : ℕ) ^ 128 := sorry

theorem polynomial_coefficient_product : 
    let a : ℝ := 1/2
    let b : ℝ := -1/2
    let c : ℝ := -1/8 in
    a * b * c = 1/32 := sorry

theorem arithmetic_progression_sum : 
    ∃ (a : ℕ → ℤ) (a₁ : ℤ), 
    (∀ n, a (n + 1) = a n + 1) ∧ 
    (∑ i in Finset.range 98, a i = 137) ∧ 
    (∑ i in Finset.filter (λ k => Even k) (Finset.range 99), a i = 93) := sorry

theorem line_intersection_sum_eq_four :
    ∃ (A : ℝ × ℝ), (A.2 * 3 = A.1) ∧ (2 * A.1 + 5 * A.2 = 11) ∧ (A.1 + A.2 = 4) := sorry

theorem prime_divides_a_pow_p_minus_a (p : ℕ) (hp : Nat.Prime p) (a : ℕ) (ha : a > 0) : p ∣ a ^ p - a := sorry

theorem f_comparison : ∃ (x : ℚ) (hx : x > 0), f x < 0 := by
  refine ⟨25/11, by norm_num, ?_⟩
  sorry

theorem equation_solution : ∃ a : ℝ, Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 ∧ a = 8 := sorry

theorem inequality_for_real_numbers (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : a * b + (a - b) ≤ 1 := sorry

theorem floor_sum_example : ∑ k in Finset.Icc 1 4, (Int.floor ((10^k : ℝ) * ((1 : ℝ)/3))) = 3702 := sorry

theorem inequality_for_positive_reals (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := sorry

theorem units_digit_product : (Nat.digits 10 (16^17 * 17^18 * 18^19)).head? = some 2 := sorry

theorem trigonometric_equation_solutions : 
    let solutions : Set ℝ := {x | x ∈ Set.Icc (0 : ℝ) π ∧ (Real.sin (π/2 * Real.cos x) = Real.cos (π/2 * Real.sin x))}
    in Fintype.card (solutions : Set ℝ) = 2 := sorry

theorem maximum_value_of_f : ∃! (t : ℝ), ∀ (x : ℝ), f x ≤ f t := sorry

theorem derivative_minimum : 
    let f : ℝ → ℝ := λ x => x ^ 2 - 14 * x + 3
    let f' : ℝ → ℝ := λ x => 2 * x - 14
    let f'' : ℝ → ℝ := λ x => 2 in
    f' 7 = 0 ∧ f'' 7 > 0 ∧ (∀ x, f 7 ≤ f x) := sorry

theorem imo_2001_sum_max : ∃ (I M O : ℕ) (hI : I > 0) (hM : M > 0) (hO : O > 0) (hdistinct : I ≠ M ∧ I ≠ O ∧ M ≠ O) 
    (hprod : I * M * O = 2001), (∀ (I' M' O' : ℕ) (hI' : I' > 0) (hM' : M' > 0) (hO' : O' > 0) 
    (hdistinct' : I' ≠ M' ∧ I' ≠ O' ∧ M' ≠ O') (hprod' : I' * M' * O' = 2001), I' + M' + O' ≤ I + M + O) ∧ I + M + O = 671 := sorry

theorem number_of_solutions_tan_2x_eq_cos_x_over_2 : 
    let solutions : Set ℝ := {x | x ∈ Set.Icc (0 : ℝ) (2 * π) ∧ Real.tan (2 * x) = Real.cos (x / 2)}
    in Finset.card (solutions.toFinite.toFinset) = 5 := sorry

theorem least_sum_m_n : ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ Nat.gcd m n = 8 ∧ Nat.lcm m n = 112 ∧ m + n = 72 := sorry

theorem final_three_digits_sum : (Nat.digits 10 (5^100)).takeLast 3 |>.sum = 13 := sorry

theorem parity_pattern : 
    let D : ℕ → ℕ := 
      Nat.rec 0 (λ _ => Nat.rec 0 (λ _ => Nat.rec 1 (λ n _ _ => D (n + 2) + D n)))
    in 
    let parity_pattern : ℕ → Bool := λ n => 
      match n % 8 with
      | 0 => false
      | 1 => false
      | 2 => true
      | 3 => true
      | 4 => true
      | 5 => false
      | 6 => true
      | _ => false
    in
    (D 2021) % 2 = 1 ∧ (D 2022) % 2 = 0 ∧ (D 2023) % 2 = 1 := sorry

theorem positive_nat_exists_with_bound : ∃ (n : ℕ), n > 0 ∧ (Real.log (n : ℝ) ^ (1 / (n : ℝ)) : ℝ) ≤ 2 - 1 / (n : ℝ) := sorry

theorem solve_abc : ∃ (a b c : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ a * (b + c) = 152 ∧ b * (c + a) = 162 ∧ c * (a + b) = 170 ∧ a * b * c = 720 := sorry

theorem division_example : 1529 / 6 = 254 ∧ 254 * 6 = 1524 ∧ 1529 - 1524 = 5 ∧ 1529 % 6 = 5 := sorry

theorem square_of_ninety_one : (91 : ℕ) * (91 : ℕ) = (8281 : ℕ) := sorry

theorem log_base_3_of_27_eq_3 : Real.logb 3 27 = 3 := sorry

theorem three_pow_three_eq_27 : (3 : ℝ) ^ (3 : ℝ) = 27 := sorry

theorem solve_for_a : (8⁻¹ / 4⁻¹) - a⁻¹ = 1 ↔ a = -2 := sorry

theorem complex_equation_solution : ∀ (z : ℂ), 12 * Complex.normSq z = 2 * Complex.normSq (z + 2) + Complex.normSq (z ^ 2 + 1) + 31 → z + 6 / z = -2 := sorry

theorem arithmetic_and_geometric_means : ∀ (x y : ℝ), (x + y) / 2 = 7 → Real.sqrt (x * y) = Real.sqrt 19 → x + y = 14 → x * y = 19 → (x + y) ^ 2 = 196 → x ^ 2 + y ^ 2 = 158 := sorry

theorem derived_equation : ∀ (r : ℝ), (Real.rpow r (1/3 : ℝ) + 1 / (Real.rpow r (1/3 : ℝ)) = 3) → (Real.rpow r 3 + 1 / (Real.rpow r 3) = 5778) := sorry

theorem exists_unique_initial_value : ∃! (x₁ : ℝ), ∀ n : ℕ, n ≥ 1 → let x := Nat.rec x₁ (λ k xₖ => xₖ * (xₖ + 1 / (k : ℝ))) n in 0 < x ∧ let x_next := x * (x + 1 / (n : ℝ)) in x < x_next ∧ x_next < 1 := sorry

theorem distance_property : ∃ (a : ℂ) (b : ℂ), a ∈ ({z : ℂ | z ^ 3 - 8 = 0} : Set ℂ) ∧ b ∈ ({z : ℂ | z ^ 3 - 8 * z ^ 2 - 8 * z + 64 = 0} : Set ℂ) ∧ 
    ∀ (x : ℂ) (y : ℂ), x ∈ ({z : ℂ | z ^ 3 - 8 = 0} : Set ℂ) → y ∈ ({z : ℂ | z ^ 3 - 8 * z ^ 2 - 8 * z + 64 = 0} : Set ℂ) → 
    Complex.dist x y ≤ Complex.dist a b ∧ Complex.dist a b = Real.sqrt 84 ∧ Real.sqrt 84 = 2 * Real.sqrt 21 := sorry

theorem divides_expression (n : ℕ) : 11 ∣ (10 : ℤ)^n - ((-1 : ℤ))^n := sorry

theorem sequence_sum_product_constraint (n : ℕ) (a : ℕ → ℝ) (h_nonneg : ∀ i, 0 ≤ a i) (h_sum : ∑ i in Finset.range n, a i = n) (h_prod : ∏ i in Finset.range n, a i ≤ 1) : True := sorry

theorem log_square_eq_20 (x y : ℝ) (hx_pos : x > 0) (hy_pos : y > 0) (hx_ne_one : x ≠ 1) (hy_ne_one : y ≠ 1)
    (h_log_eq : Real.logb 2 x = Real.logb y 16) (h_product : x * y = 64) : 
    ((Real.logb 2 (x / y)) ^ 2 = 20) := sorry

theorem solve_for_c : c = 3 := by
  intro hf : ∀ x, f x = c * x ^ 3 - 9 * x + 3
  intro hf2 : f 2 = 9
  have h1 : f 2 = c * (2 : ℝ) ^ 3 - 9 * (2 : ℝ) + 3 := hf 2
  rw [hf2] at h1
  have h2 : (2 : ℝ) ^ 3 = (8 : ℝ) := by norm_num
  rw [h2] at h1
  have h3 : c * (8 : ℝ) - 9 * (2 : ℝ) + 3 = c * (8 : ℝ) - 15 := by ring
  rw [h3] at h1
  have h4 : c * (8 : ℝ) - 15 = 9 := by linarith
  have h5 : c * (8 : ℝ) = 24 := by linarith
  have h6 : c = 3 := by linarith
  exact h6 := sorry

theorem inequality_for_real_x_and_nat_n (x : ℝ) (n : ℕ) (hx : x > -1) : 1 + (n : ℝ) * x ≤ (1 + x) ^ n := sorry

theorem congruence_result : ∃ n : ℤ, 0 ≤ n ∧ n < 101 ∧ 123456 ≡ n [ZMOD 101] ∧ n = 34 := sorry

theorem son_age_today : ∃ (sonAgeToday : ℕ), sonAgeToday = 6 := by
  refine ⟨6, ?_⟩
  sorry

theorem arithmetic_series_first_term : 
    ∀ (a d : ℚ), (∑ k in Finset.range 5, (a + (k : ℚ) * d)) = 70 → (∑ k in Finset.range 10, (a + (k : ℚ) * d)) = 210 → a = 42/5 := sorry

theorem remainder_calculation : (121 * 122 * 123) % 4 = 2 := sorry

theorem sum_one_to_twelve_eq_seventy_eight : (Finset.sum (Finset.Icc 1 12) fun n : ℕ => n) = 78 := sorry

theorem seventy_eight_mod_four_eq_two : 78 % 4 = 2 := sorry

theorem expression_value_at_x_eq_4 : (fun (x : ℝ) => (3*x - 2)*(4*x + 1) - (3*x - 2)*4*x + 1) (4 : ℝ) = (11 : ℝ) := sorry

theorem absolute_value_equation_sum : 
    let solutions : Set ℝ := {x | |2 - x| = 3}
    in solutions = {-1, 5} ∧ (-1 : ℝ) + 5 = 4 := sorry

theorem equation_product_of_roots : 
    let y := fun (x : ℝ) => x^2 + 18*x + 45 in
    let equation := fun (x : ℝ) => x^2 + 18*x + 30 = 2 * Real.sqrt (x^2 + 18*x + 45) in
    let roots := {x : ℝ | equation x} in
    let quadratic := fun (x : ℝ) => x^2 + 18*x + 20 in
    let real_roots := {x : ℝ | quadratic x = 0} in
    ∏ x in real_roots, x = 20 := sorry

theorem f_value_at_3 : f 3 = 8 := sorry

theorem find_a_minus_d : ∃ (a b c d : ℕ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a * b * c * d = 40320 ∧ a * b + a + b = 524 ∧ b * c + b + c = 146 ∧ c * d + c + d = 104 ∧ a - d = 10 := sorry

theorem base_three_1222_equals_fifty_three : (1222 : ℕ) = 53 := sorry

theorem power_congruence : ∀ (n : ℕ) (hn : n ≥ 1), 3^(2^n) - 1 ≡ 2^(n+2) [MOD 2^(n+3)] := sorry

theorem arithmetic_sequence_terms : 
    ∃ (a : ℕ → ℝ) (d : ℝ), 
      a 7 = 30 ∧ a 11 = 60 ∧ d = 7.5 ∧ a 21 = 135 ∧ ∀ n, a (n + 1) = a n + d := sorry

theorem f_of_84 : f 84 = 997 := sorry

theorem find_all_functions : {f : ℤ → ℤ | ∀ (a b : ℤ), f (2 * a) + 2 * f b = f (f (a + b))} = {f | ∀ (x : ℤ), f x = 0} := sorry

theorem composition_result : f (g 2) = 8 := sorry

theorem ordered_pair_satisfies_equations : ∃ (a b : ℤ), (3 * a + 2 * b = 5) ∧ (a + b = 2) ∧ (a, b) = (1, 1) := sorry

theorem prime_operation_result : ∃ (p q : ℕ), p ∈ ({x | Nat.Prime x} : Set ℕ) ∩ (Set.Ioo (4 : ℕ) 18) ∧ q ∈ ({x | Nat.Prime x} : Set ℕ) ∩ (Set.Ioo (4 : ℕ) 18) ∧ p ≠ q ∧ p * q - (p + q) = 119 := sorry

theorem marble_puzzle : (239 + 174 + 83) % 10 = 6 := sorry

theorem f_property : ∃ (f : ℕ → ℕ → ℕ), (∀ (x : ℕ), f x x = x) ∧ (∀ (x y : ℕ), f x y = f y x) ∧ (∀ (x y : ℕ), (x + y) * f x y = y * f x (x + y)) ∧ f 14 52 = 364 := sorry

theorem cube_root_computation : (Real.log 8) = Real.log 8 ∧ (Real.rpow (8 : ℝ) ((2 : ℝ)/3)) = (2 : ℝ) ∧ (16 : ℝ) * (2 : ℝ) = (32 : ℝ) ∧ (Real.rpow (32 : ℝ) ((1 : ℝ)/3)) = (4 : ℝ) ∧ (4 : ℝ) = (4 : ℝ) := sorry

theorem square_root_product_simplification (x : ℝ) (hx : x ≥ 0) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := sorry

theorem jasmine_water_consumption : ∃ (firstThreeMilesWater : ℚ) (rate : ℚ) (additionalMiles : ℕ) (additionalWater : ℚ),
    firstThreeMilesWater = 1.5 ∧ rate = 0.5 ∧ additionalMiles = 10 ∧ additionalWater = 5 ∧
    additionalWater = rate * (additionalMiles : ℚ) := sorry

theorem number_of_solutions : Fintype.card {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) (2 * π) ∧ 1 - 3 * Real.sin θ + 5 * Real.cos (3 * θ) = 0} = 6 := sorry

theorem expression_simplification : Real.log 6 / Real.log 2 + Real.log 6 / Real.log 3 = (Real.sqrt (Real.log 3 / Real.log 2) + Real.sqrt (Real.log 2 / Real.log 3)) ^ 2 := sorry

theorem inequality_power_mean : ∀ (a b : ℝ) (h₁ : a > 0) (h₂ : b > 0) (n : ℕ) (h₃ : n > 0), ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := sorry

theorem find_ax5_by5 (a b x y : ℝ) (h1 : a * x + b * y = 3) (h2 : a * x ^ 2 + b * y ^ 2 = 7) 
    (h3 : a * x ^ 3 + b * y ^ 3 = 16) (h4 : a * x ^ 4 + b * y ^ 4 = 42) : a * x ^ 5 + b * y ^ 5 = 20 := sorry

theorem periodic_function_exists : ∃ (a : ℝ), 0 < a ∧ ∃ (f : ℝ → ℝ), (∀ (x : ℝ), f (x + a) = 1/2 + Real.sqrt (f x - (f x)^2)) → ∃ (b : ℝ), 0 < b ∧ ∀ (x : ℝ), f (x + b) = f x := sorry

theorem units_digit_of_sum : ((29 : ℕ) * 79 + 31 * 81) % 10 = 2 := sorry

theorem division_with_remainder : 194 / 11 = 17 ∧ 194 % 11 = 7 := sorry

theorem real_inequalities (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : a + b + c = 2) (h4 : a * b + b * c + c * a = 1) : 
    0 ≤ a ∧ a ≤ 1/3 ∧ 1/3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4/3 := sorry

theorem integer_solutions_count : Finset.card (Finset.Icc (-9 : ℤ) 9) = 19 := sorry

theorem find_difference : ∃ (x y : ℕ), x + y = 17402 ∧ 10 ∣ x ∧ y = x / 10 ∧ (x - y = 15822 ∨ y - x = 15822) := sorry

theorem recurrence_sum : ∃ (a b : ℕ → ℝ), (∀ n, (a (n + 1), b (n + 1)) = (Real.sqrt 3 * a n - b n, Real.sqrt 3 * b n + a n)) ∧ (a 100, b 100) = (2, 4) ∧ a 1 + b 1 = 1 / 2^98) := sorry

theorem positive_integer_solutions_exist : ∃ (m n : ℕ) (hm : Nat.Prime m) (hn : Nat.Prime n) (k t : ℕ), 
    k > 0 ∧ t > 0 ∧ k > t ∧ 
    k^2 - m * k + n = 0 ∧ t^2 - m * t + n = 0 ∧ 
    m^n + n^m + k^t + t^k = 20 := sorry

theorem consecutive_even_integers_product_288 :
    ∃ (x : ℕ), 0 < x ∧ Even x ∧ Even (x + 2) ∧ x * (x + 2) = 288 ∧ x = 16 := sorry

theorem sum_of_roots : ∃ (a b : ℝ), a > 0 ∧ b > 0 ∧ a ≠ b ∧ ((a - 1/a = 1 ∧ b - 1/b = -1) ∨ (a - 1/a = -1 ∧ b - 1/b = 1)) ∧ a + b = Real.sqrt 5 := sorry

theorem triangle_inequality_expression (a b c : ℝ) (h : a + b > c ∧ b + c > a ∧ c + a > b) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := sorry

theorem polynomial_coefficient_B : 
    ∃ (roots : Multiset ℕ) (p : ℤ[X]), 
      p = (X - 1)^2 * (X - 2)^4 ∧ 
      p = X^6 - 10*X^5 + 41*X^4 - 88*X^3 + 104*X^2 - 64*X + 16 ∧ 
      Multiset.prod (roots.map (λ r => X - (C (r : ℤ)))) = p ∧ 
      roots.card = 6 ∧ 
      (∀ r ∈ roots, r ∈ ({1, 2, 4, 8, 16} : Set ℕ)) ∧ 
      Multiset.prod (roots.map (λ r => (r : ℤ))) = (16 : ℤ) ∧ 
      Multiset.sum (roots.map (λ r => (r : ℤ))) = (10 : ℤ) := sorry

theorem find_sum_of_a_plus_b (a b : ℝ) (h1 : a ^ 2 * b ^ 3 = 32/27) (h2 : a / b ^ 3 = 27/4) : a + b = 8/3 := sorry

theorem arithmetic_sequence_problem : ∃ (x n : ℕ), (2*x - 3) + ((5*x - 11) - (2*x - 3)) = (5*x - 11) ∧ (5*x - 11) + ((3*x + 1) - (5*x - 11)) = (3*x + 1) ∧ (5*x - 11) - (2*x - 3) = (3*x + 1) - (5*x - 11) ∧ x = 4 ∧ n = 502 := sorry

