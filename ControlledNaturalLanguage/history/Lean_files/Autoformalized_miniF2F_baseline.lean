
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


theorem problem_solution : ∃ (a b c d : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0), 
    a * b * c * d = Nat.factorial 8 ∧ a * b + a + b = 524 ∧ b * c + b + c = 146 ∧ c * d + c + d = 104 ∧ a - d = 10 := sorry

theorem intersection_points : ∃ (m n : ℝ), (∀ (x : ℝ), x^4 = 5*x^2 - 6 ↔ (x = Real.sqrt m ∨ x = -Real.sqrt m ∨ x = Real.sqrt n ∨ x = -Real.sqrt n)) ∧ m > n ∧ m - n = 1 := sorry

theorem count_integers_divisible_by_twenty : Finset.card (Finset.filter (λ x : ℤ => 20 ∣ x) (Finset.Icc (15 : ℤ) 85)) = 4 := sorry

theorem area_change : (3491 - 60) * (3491 + 60) - 3491 * 3491 = 3600 := sorry

theorem ones_digit_product : (Nat.digits 10 (1 * 3 * 5 * 7 * 9 * 11 * 13)).head? = some 5 := sorry

theorem odd_square_plus_multiple_of_four_square_mod_eight (a : ℤ) (b : ℕ) (ha : Odd a) (hb : 4 ∣ b) : a^2 + (b : ℤ)^2 ≡ 1 [ZMOD 8] := sorry

theorem n_root_n_le_two_minus_one_over_n (n : ℕ) (hn : n > 0) : (Real.log n) / (n : ℝ) ≤ Real.log (2 - 1 / (n : ℝ)) := sorry

theorem max_value_of_expression : 
    ∃ (t_max : ℝ), (∀ (t : ℝ), ((2.0 ^ t - 3.0 * t) * t) / (4.0 ^ t) ≤ ((2.0 ^ t_max - 3.0 * t_max) * t_max) / (4.0 ^ t_max)) ∧ 
    ((2.0 ^ t_max - 3.0 * t_max) * t_max) / (4.0 ^ t_max) = 1/12 := sorry

theorem star_operation_result : (3 : ℚ) ⋆ (11 : ℚ) = (1 : ℚ) / 33 := sorry

theorem digit_for_multiple_of_eleven : ∃! d : Fin 10, (2007 + 10 * d.val) % 11 = 0 := sorry

theorem min_value_of_quadratic : ∃ x, (∀ y, x^2 - 14*x + 3 ≤ y^2 - 14*y + 3) ∧ x = 7 := sorry

theorem remainder_of_twice_when_mod_five_is_three : ∀ (n : ℕ), n % 5 = 3 → (2 * n) % 5 = 1 := sorry

theorem lcm_gcd_problem : ∃ (x : ℕ), lcm 120 x = 3720 ∧ gcd 120 x = 8 ∧ x = 248 := sorry

theorem problem_solution : ∃ (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0), 
    x + 1/y = 4 ∧ y + 1/z = 1 ∧ z + 1/x = 7/3 ∧ x * y * z = 1 := sorry

theorem f_properties_and_value : 
    ∃ (f : ℕ → ℕ → ℕ) (h1 : ∀ x, f x x = x) (h2 : ∀ x y, f x y = f y x) (h3 : ∀ x y, (x + y) * f x y = y * f x (x + y)), 
    f 14 52 = 364 := sorry

theorem product_of_odd_integers_less_than_10000 : 
    ∏ k in Finset.Ico 1 10000 | 2 ∤ k, k = (Nat.factorial 10000) / ((2 : ℕ) ^ 5000 * Nat.factorial 5000) := sorry

theorem sum_reciprocal_sqrt_lt_198 : ∑ k in Finset.Icc 2 10000, (1 : ℝ) / Real.sqrt k < 198 := sorry

theorem plumbing_charge : ∃ (N x : ℕ), (N + 1 * x = 97) ∧ (N + 5 * x = 265) ∧ (N + 2 * x = 139) := sorry

theorem product_eq_2005_sum_eq_406 : ∃ (a b : ℕ), a > 1 ∧ b > 1 ∧ a * b = 2005 ∧ a + b = 406 := sorry

theorem problem_statement : ∀ (m n : ℤ), (12 : ℝ) ^ (m * n) = ((2 : ℝ) ^ m) ^ (2 * n) * ((3 : ℝ) ^ n) ^ m := sorry

theorem divides_pow_sub (p : ℕ) (hp : Nat.Prime p) (a : ℕ) (ha : a > 0) : p ∣ a ^ p - a := sorry

theorem problem_2002_amc_12b_22 : Set.Infinite {m : ℕ | m > 0 ∧ ∃ n : ℕ, n > 0 ∧ m * n ≤ m + n} := sorry

theorem problem_value : ((3 * (4 : ℝ) - 2) * (4 * (4 : ℝ) + 1) - ((3 * (4 : ℝ) - 2) * 4 * (4 : ℝ)) + 1) = (11 : ℝ) := sorry

theorem largest_negative_solution : ∃! x : ℤ, x < 0 ∧ 24 * x % 1199 = 15 % 1199 ∧ ∀ y : ℤ, y < 0 ∧ 24 * y % 1199 = 15 % 1199 → y ≤ x := sorry

theorem inequality_of_positive_reals (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) :
    a ^ 2 / b + b ^ 2 / c + c ^ 2 / d + d ^ 2 / a ≥ a + b + c + d := sorry

theorem count_integer_solutions_abs_x_lt_3pi : Finset.card (Finset.filter (λ x : ℤ => |x| < 3 * π) Finset.univ) = 19 := sorry

theorem arithmetic_sequence_problem : ∃ (a d : ℤ), (a + 6 * d = 30) ∧ (a + 10 * d = 60) ∧ (a + 20 * d = 135) := sorry

theorem integer_functional_equation : 
    {f : ℤ → ℤ} → (∀ a b : ℤ, f (2 * a) + 2 * f b = f (f (a + b))) → 
    (∀ x : ℤ, f x = 0) ∨ (∀ x : ℤ, f x = 2 * x) := sorry

theorem problem_solution : 100 * A + 10 * B + C = 129 := sorry

theorem inequality_for_positive_reals (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := sorry

theorem base9_to_base10 : (0x852 : ℕ) = 695 := sorry

theorem son_age_today : ∃ (father_age son_age : ℕ), father_age = 5 * son_age ∧ (father_age - 3) + (son_age - 3) = 30 ∧ son_age = 6 := sorry

theorem sum_units_digits_multiples_of_three : 
    let multiples := Finset.filter (λ n : ℕ => n % 3 = 0) (Finset.Ico 0 51) in
    Finset.sum multiples (λ n => n % 10) = 78 := sorry

theorem remainder_of_100th_fibonacci_mod_4 : (Nat.fib 100) % 4 = 3 := sorry

theorem marbles_removal_needed : 
    let total_marbles := 239 + 174 + 83
    let remainder := total_marbles % 10
    in remainder = 6 := sorry

theorem div_by_twelve : ∀ n : ℕ, 12 ∣ 4^(n + 1) + 20 := sorry

theorem expand_and_show : (x + 3) * (2 * x - 6) = 2 * x ^ 2 - 18 := sorry

theorem problem_solution : B = -88 := sorry

theorem amc_sum_problem : A + M + C = 14 := sorry

theorem remainder_of_54_mod_6 : 54 % 6 = 0 := sorry

theorem function_condition_implies_identity (f : ℕ → ℕ) (hpos : ∀ n, f n > 0) (hineq : ∀ n, f (n + 1) > f (f n)) : ∀ n, f n = n := sorry

theorem problem_solution : ∃ (f : ℚ → ℚ) (h_additive : ∀ (a b : ℚ), 0 < a → 0 < b → f (a * b) = f a + f b) (h_prime : ∀ (p : ℕ), Nat.Prime p → f (p : ℚ) = (p : ℚ)), 
    (f (17/32 : ℚ) < 0) ∧ (f (11/16 : ℚ) < 0) ∧ (f (7/9 : ℚ) < 0) ∧ (f (7/6 : ℚ) < 0) ∧ ¬(f (25/11 : ℚ) < 0) := sorry

theorem father_age_base_ten : ((1 : ℕ) * 3 ^ 3 + (2 : ℕ) * 3 ^ 2 + (2 : ℕ) * 3 ^ 1 + (2 : ℕ) * 3 ^ 0) = 53 := sorry

theorem exists_multiplicative_inverse_mod_1399 : ∃ n : ℤ, 0 ≤ n ∧ n < 1399 ∧ (160 * n) % 1399 = 1 := by
  refine ⟨1058, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · native_decide

theorem consecutive_sums : 
    let even_ints := λ (x : ℤ) => Finset.sum (Finset.Icc x (x + 8)) (λ n => if Even n then n else 0) in
    let odd_sum := Finset.sum (Finset.Icc 1 8) (λ n => if Odd n then n else 0) in
    ∃ (x : ℤ), even_ints x = odd_sum - 4 ∧ x = 8 := sorry

theorem remainder_of_f_94 : (f 94) % 1000 = 561 := sorry

theorem problem_statement : ∀ (a b : ℝ), (∀ (x : ℝ), f a b x = a * x ^ 4 - b * x ^ 2 + x + 5) → f a b (-3) = 2 → f a b 3 = 8 := sorry

theorem find_inverse_mod_121 : ∃ b : ℕ, b < 11^2 ∧ 24 * b % (11^2) = 1 := sorry

theorem cone_volume_formula : 
    let B : ℝ := 30
    let h : ℝ := 6.5
    let V : ℝ := (1/3 : ℝ) * B * h
    in V = 65 := sorry

theorem circle_radius : ∃ (center : ℝ × ℝ) (radius : ℝ), radius = 5 ∧ ∀ (x y : ℝ), x^2 + 8*x + y^2 - 6*y = 0 → (x - center.1)^2 + (y - center.2)^2 = radius^2 := sorry

theorem sum_of_coordinates_of_intersection : 
    ∃ (A : ℝ × ℝ), (3 * A.2 = A.1) ∧ (2 * A.1 + 5 * A.2 = 11) ∧ (A.1 + A.2 = 4) := sorry

theorem exists_integer_mul_pi_diff (n : ℕ) (a : ℕ → ℝ) (x₁ x₂ : ℝ) (hx₁ : f n a x₁ = 0) (hx₂ : f n a x₂ = 0) : ∃ (m : ℤ), x₂ - x₁ = π * (m : ℝ) := sorry

theorem remainder_of_1529_mod_6 : 1529 % 6 = 5 := sorry

theorem product_bound (n : ℕ) (a : ℕ → ℝ) (ha_nonneg : ∀ i, 0 ≤ a i) (h_sum : ∑ i in Finset.range n, a i = n) : 
    ∏ i in Finset.range n, a i ≤ 1 := sorry

theorem simplify_expression (x : ℝ) (hx : x ≠ 0) : (12 / (x * x)) * (x ^ 4 / (14 * x)) * (35 / (3 * x)) = 10 := sorry

theorem ordered_pair_solution : ∃ (a b : ℝ), 3 * a + 2 * b = 5 ∧ a + b = 2 ∧ (a, b) = (1, 1) := sorry

theorem remainder_of_194_mod_11 : 194 % 11 = 7 := sorry

theorem remainder_of_expression : (129 ^ 34 + 96 ^ 38) % 11 = 9 := sorry

theorem solve_equation : ∃ x : ℝ, (x - 9) / (x + 1) = 2 ∧ x = -11 := sorry

theorem four_digit_divisible_by_18 : ∃ n : Fin 10, (374 * 10 + n).val % 18 = 0 ∧ n.val = 4 := sorry

theorem expression_value : ((100 : ℝ)^2 - (7 : ℝ)^2) / ((70 : ℝ)^2 - (11 : ℝ)^2) * (((70 : ℝ) - 11) * ((70 : ℝ) + 11)) / (((100 : ℝ) - 7) * ((100 : ℝ) + 7)) = (1 : ℝ) := sorry

theorem problem_2000_amc_12_24 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h1 : a * (b + c) = 152) (h2 : b * (c + a) = 162) (h3 : c * (a + b) = 170) : a * b * c = 720 := sorry

theorem floor_sum_of_multiples_of_one_third : 
    let N : ℝ := 1/3 in 
    (Int.floor (10 * N) : ℤ) + (Int.floor (100 * N) : ℤ) + (Int.floor (1000 * N) : ℤ) + (Int.floor (10000 * N) : ℤ) = 3702 := sorry

theorem problem_solution : ∃ (p q : ℕ) (hp : p > 0) (hq : q > 0) (hcoprime : Nat.Coprime p q), 
    let a : ℝ := (p : ℝ) / q in
    let floor : ℝ → ℤ := λ x => Int.floor x in
    let fract : ℝ → ℝ := λ x => x - (floor x : ℝ) in
    let S : Set ℝ := {x | (floor x : ℝ) * fract x = a * x ^ 2} in
    ∑ x in S, x = 420 ∧ p + q = 929 := sorry

theorem divisibility_condition (n : ℕ) : 11 ∣ (10 ^ n - (-1 : ℤ) ^ n) := sorry

theorem arithmetic_sequence_y_value : y = 9 := sorry

theorem no_integer_solutions : ¬∃ (x y : ℤ), 4 * x ^ 3 - 7 * y ^ 3 = 2003 := sorry

theorem problem : let f : ℤ → ℤ := λ x => 2 * x - 3; g : ℤ → ℤ := λ x => x + 1 in g (f 5 - 1) = 7 := sorry

theorem possible_result_of_product_minus_sum : 
    ∃ (p q : ℕ), Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ 4 < p ∧ p < 18 ∧ 4 < q ∧ q < 18 ∧ 
    (p * q - (p + q) = 119) := sorry

theorem arithmetic_sequence_nth_term : 
    ∃ (x n : ℕ), (2*x - 3) + (n-1) * ((5*x - 11) - (2*x - 3)) = 2009 ∧ n = 502 := sorry

theorem sum_of_last_three_digits_of_5_pow_100 : (Nat.digits 10 (5 ^ 100)).reverse.take 3 |>.sum = 13 := sorry

theorem five_plus_500_percent_of_ten_is_110_percent_of_fifty : (5 + (500 : ℝ) / 100 * 10) = (110 : ℝ) / 100 * 50 := sorry

theorem problem_statement : ∃ (k m n : ℕ) (hk : k > 0) (hm : m > 0) (hn : n > 0) (hcoprime : Nat.Coprime m n), 
    (∀ (t : ℝ), (1 + Real.sin t) * (1 + Real.cos t) = (5 : ℝ)/4 → (1 - Real.sin t) * (1 - Real.cos t) = (m : ℝ)/n - Real.sqrt k) ∧ 
    k + m + n = 27 := sorry

theorem units_digit_sum_squares_first_nine : (∑ i in Finset.Icc 1 9, i^2) % 10 = 5 := sorry

theorem smallest_positive_integer_cube_fourth_power : 
    ∃ n : ℕ, n > 1 ∧ (∃ k : ℕ, k ^ 3 = n) ∧ (∃ m : ℕ, m ^ 4 = n) ∧ 
    ∀ n' : ℕ, n' > 1 ∧ (∃ k' : ℕ, k' ^ 3 = n') ∧ (∃ m' : ℕ, m' ^ 4 = n') → n ≤ n' := sorry

theorem count_solutions : Finset.card (Finset.filter (λ n : ℕ => (n + 1000) / 70 = Nat.floor (Real.sqrt n)) (Finset.Icc 1 1000000)) = 6 := sorry

theorem f_value : f 84 = 997 := sorry

theorem solve_geometric_sequences (a b : ℝ) (ha_pos : 0 < a) (hb_pos : 0 < b) 
    (h_seq1 : ∃ r : ℝ, a = 6 * r ∧ b = a * r) 
    (h_seq2 : ∃ s : ℝ, a = (1 / b) * s ∧ 54 = a * s) : 
    a = 3 * Real.sqrt 2 := sorry

theorem consecutive_even_product : ∃ (n : ℕ), 0 < n ∧ Even n ∧ Even (n + 2) ∧ (n * (n + 2) = 288) ∧ (n + 2 = 18) := sorry

theorem sum_of_digits : ∃ (A B C : ℕ), 1 ≤ A ∧ A ≤ 9 ∧ 1 ≤ B ∧ B ≤ 9 ∧ 1 ≤ C ∧ C ≤ 9 ∧ A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ A + B = C ∧ (10 * A + A) - B = 2 * C ∧ C * B = (10 * A + A) + A ∧ A + B + C = 8 := sorry

theorem gcd_lcm_sum_min : ∃ (m n : ℕ), 0 < m ∧ 0 < n ∧ Nat.gcd m n = 8 ∧ Nat.lcm m n = 112 ∧ m + n = 72 := sorry

theorem number_of_solutions_tan2x_eq_cos_halfx : 
    let interval : Set ℝ := Set.Icc (0 : ℝ) (2 * π) in
    let solutions : Set ℝ := {x | x ∈ interval ∧ Real.tan (2 * x) = Real.cos (x / 2)} in
    Finset.card (solutions.toFinite.toFinset) = 5 := sorry

theorem parity_sequence : (Nat.ModEq 2 (D 2021) 0 ∧ Nat.ModEq 2 (D 2022) 1 ∧ Nat.ModEq 2 (D 2023) 0) := sorry

theorem exists_unique_initial_value : ∃! (x₁ : ℝ), ∀ n : ℕ, n ≥ 1 → let x := Nat.rec x₁ (fun k x_k => x_k * (x_k + (1 : ℝ) / (k + 1))) n in 0 < x ∧ x < 1 ∧ x < x * (x + (1 : ℝ) / (n + 1)) := sorry

theorem gcd_lcm_sum_min : ∃ (m n : ℕ) (hm : m > 0) (hn : n > 0), Nat.gcd m n = 6 ∧ Nat.lcm m n = 126 ∧ m + n = 60 ∧ ∀ (x y : ℕ) (hx : x > 0) (hy : y > 0), Nat.gcd x y = 6 → Nat.lcm x y = 126 → 60 ≤ x + y := sorry

theorem inequality_of_power_means (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) (hn : 0 < n) : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := sorry

theorem sum_of_nice_numbers : 
    let nice_numbers : Set ℕ := {n | ∃ (m : ℕ), m > 0 ∧ Finset.card (Nat.divisors m) = 4 ∧ ∑ d in Nat.divisors m, d = n}
    in ∑ n in (Finset.Icc 2010 2019).filter (λ n => n ∈ nice_numbers), n = 2016 := sorry

theorem number_of_solutions_in_interval : 
    let solutions : Set ℝ := {x | x ∈ Set.Icc (0 : ℝ) π ∧ Real.sin ((π / 2) * Real.cos x) = Real.cos ((π / 2) * Real.sin x)} in
    Finset.card (solutions.toFinite.toFinset) = 2 := sorry

theorem last_year_enrollment : ∃ (lastYearEnrollment : ℕ), lastYearEnrollment * 104 / 100 = 598 ∧ lastYearEnrollment = 575 := sorry

theorem units_digit_product_odd_between_zero_and_twelve : (∏ x in Finset.Ico 1 12, if Odd x then x else 1) % 10 = 5 := sorry

theorem smallest_square_cube_above_ten : 
    let candidates := {x : ℕ | x > 10 ∧ ∃ n : ℕ, n^2 = x ∧ ∃ m : ℕ, m^3 = x} in
    (Nat.find (Set.Nonempty_of_mem ?_)) = 64 := sorry

theorem odd_integers_condition (a b c d : ℤ) (ha : Odd a) (hb : Odd b) (hc : Odd c) (hd : Odd d) (hpos : 0 < a) (hlt : a < b ∧ b < c ∧ c < d) (had : a * d = b * c) (hk : ∃ k : ℤ, a + d = 2 ^ k) (hm : ∃ m : ℤ, b + c = 2 ^ m) : a = 1 := sorry

theorem problem_solution : ∃ (a b : ℝ) (ha : a > 0) (hb : b > 0) (hne : a ≠ b), (|a - (1 / a)| = 1 ∧ |b - (1 / b)| = 1) ∧ a + b = Real.sqrt 5 := sorry

theorem complex_equation_solution : ∃ (z : ℂ), (12 : ℂ) * Complex.normSq z = (2 : ℂ) * Complex.normSq (z + 2) + Complex.normSq (z ^ 2 + 1) + (31 : ℂ) ∧ z + 6 / z = (-2 : ℂ) := sorry

theorem consecutive_integers_product_eq_eight_times_sum_squares_sum : 
    ∃ (x : ℕ) (hx : x > 0), 
      x * (x + 1) * (x + 2) = 8 * (x + (x + 1) + (x + 2)) ∧ 
      x^2 + (x + 1)^2 + (x + 2)^2 = 77 := sorry

theorem log_problem (x y z : ℝ) (w : ℝ) (hx : 1 < x) (hy : 1 < y) (hz : 1 < z) (hw : 0 < w) 
    (h1 : Real.logb x w = 24) (h2 : Real.logb y w = 40) (h3 : Real.logb (x * y * z) w = 12) : 
    Real.logb z w = 60 := sorry

theorem smallest_k_such_that_for_all_n_gcd_conditions : 
    let candidates := Finset.Icc 1 6 in
    let condition (k : ℕ) : Prop := ∀ n : ℕ, 0 < n → 
      Nat.Coprime (6 * n + k) (6 * n + 3) ∧ 
      Nat.Coprime (6 * n + k) (6 * n + 2) ∧ 
      Nat.Coprime (6 * n + k) (6 * n + 1) in
    have h : ∃ k, k ∈ candidates ∧ condition k := by
      refine ⟨5, by simp [candidates], ?_⟩
      intro n hn
      have pos : 0 < n := hn
      refine ⟨?_, ?_, ?_⟩
      · exact Nat.Coprime.symm (Nat.Coprime_add_mul_right_right 1 (by omega))
      · exact Nat.Coprime.symm (Nat.Coprime_add_mul_right_right 3 (by omega))
      · exact Nat.Coprime.symm (Nat.Coprime_add_mul_right_right 4 (by omega))
    let minimal_k := (candidates.filter condition).min' (by
      obtain ⟨k, hk, _⟩ := h
      exact Finset.Nonempty_of_mem_filter ⟨hk, ?_⟩) in
    minimal_k = 5 := sorry

theorem composition_value : (fun (x : ℝ) => x + 1) ((fun (x : ℝ) => x ^ 2 + 3) (2 : ℝ)) = (8 : ℝ) := sorry

theorem find_b_power_a (a b : ℕ) (h1 : 2 ^ a = 32) (h2 : a ^ b = 125) : b ^ a = 243 := sorry

theorem smallest_X : ∃ X : ℕ, 0 < X ∧ (∃ k : ℕ, X = 3 * k + 2) ∧ (∃ m : ℕ, X % 10 = (5 * m + 4) % 10) ∧ (∀ Y : ℕ, 0 < Y → (∃ k' : ℕ, Y = 3 * k' + 2) → (∃ m' : ℕ, Y % 10 = (5 * m' + 4) % 10) → X ≤ Y) ∧ X = 14 := sorry

