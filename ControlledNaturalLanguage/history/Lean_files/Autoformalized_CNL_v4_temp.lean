
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


theorem odd_integer_conditions_imply_a_eq_one (a b c d k m : ℤ) (ha : Odd a) (hb : Odd b) (hc : Odd c) (hd : Odd d) (hpos : 0 < a) (hlt : a < b ∧ b < c ∧ c < d) (hmul : a * d = b * c) (hsum1 : a + d = 2 ^ k) (hsum2 : b + c = 2 ^ m) : a = 1 := sorry

theorem abs_div_one_plus_abs_add_le_sum {a b : ℝ} : 
    |a + b| / (1 + |a + b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := sorry

theorem multiplicative_inverse_condition (n : ℤ) (hn1 : 0 ≤ n) (hn2 : n < 1399) (h : (35 : ℤ) * 40 = 1400) : n * 160 ≡ 1 [ZMOD 1399] := sorry

theorem not_prime_sum_product (K L M N : ℕ) (hK : K > 0) (hL : L > 0) (hM : M > 0) (hN : N > 0) 
  (hKL : K > L) (hLM : L > M) (hMN : M > N) 
  (h_eq : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) : 
  ¬ Nat.Prime (K * L + M * N) := sorry

theorem inequality_proof (x : ℝ) (y : ℝ) (z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := sorry

theorem exists_int_satisfying_congruences : ∃ (n : ℤ), 2 * n ≡ 15 [ZMOD 47] ∧ n ≡ 31 [ZMOD 47] := sorry

theorem residue_condition (b : ℤ) (hprime : Nat.Prime 11) : ∃ b' : ℤ, b' ≡ b [ZMOD 121] ∧ 24 * b' ≡ 1 [ZMOD 121] ∧ 0 ≤ b' ∧ b' < 121 := sorry

theorem solve_system : ∀ (x y z : ℝ), 3 * x + y = 17 → 5 * y + z = 14 → 3 * x + 5 * z = 41 → x + y + z = 12 := sorry

theorem goal_statement : f (f (f (f (f 4)))) = 1 := sorry

where
  f (n : ℤ) : ℤ :=
    if n % 2 = 1 then n ^ 2 else n ^ 2 - 4 * n - 1

theorem perfect_square_expression (n : ℤ) (hn : n ≥ 9) : ∃ (k : ℤ), ((Nat.factorial (n + 2) : ℤ) - (Nat.factorial (n + 1) : ℤ)) / (Nat.factorial n : ℤ) = k ^ 2 := sorry

theorem exist_irrational_power_rational : ∃ (a b : ℝ), Irrational a ∧ Irrational b ∧ Rational (a ^ b) := sorry

theorem smallest_k_satisfies_conditions :
    let candidates : Set ℕ := {k | 0 < k ∧ ∀ n : ℕ, 0 < n → Nat.gcd (6 * n + k) (6 * n + 3) = 1 ∧ Nat.gcd (6 * n + k) (6 * n + 2) = 1 ∧ Nat.gcd (6 * n + k) (6 * n + 1) = 1}
    in (∃ k, k ∈ candidates) ∧ (∀ m, m ∈ candidates → 5 ≤ m) ∧ (5 ∈ candidates) := sorry

theorem count_four_digit_even_divisible_by_five : 
    let evenDigits : Set ℕ := {0, 2, 4, 6, 8} in
    Finset.card (Finset.filter (λ D : ℕ ↦ 
      D ≥ 1000 ∧ D ≤ 9999 ∧ 
      (∀ d : ℕ, d ∈ (Nat.digits 10 D) → d ∈ evenDigits) ∧ 
      D % 5 = 0) 
    (Finset.Icc 1000 9999)) = 100 := sorry

theorem product_of_sums_equals_21000 : 
    let S1 := ∑ k in Finset.Icc 1 20, Real.log ((k^2 : ℝ) * Real.log 3) / Real.log ((5 : ℝ) ^ k) in
    let S2 := ∑ k in Finset.Icc 1 100, Real.log ((25 : ℝ) ^ k) / Real.log ((9 : ℝ) ^ k) in
    S1 * S2 = 21000 := sorry

theorem sum_reciprocal_sqrt_lt : ∑ k in Finset.Icc 2 10000, (1 : ℝ) / Real.sqrt (k : ℝ) < 198 := sorry

theorem smallest_n_with_gcd_gt_one : 
    let p (n : ℕ) : ℕ := n^2 - n + 41 in
    IsLeast {n : ℕ | 0 < n ∧ 1 < Nat.gcd (p n) (p (n + 1))} 41 := sorry

theorem factor_identity_goal (A B : ℤ) (h : ∀ (x : ℝ), 10*x^2 - x - 24 = (A*x - 8)*(B*x + 3)) : A*B + B = 12 := sorry

theorem inequality_proof (a : ℝ) (b : ℝ) (ha : a > 0) (hb : b > 0) (hle : b ≤ a) : 
    (a + b)/2 - Real.sqrt (a * b) ≤ (a - b)^2/(8 * b) := sorry

theorem perfect_square_divisors_count :
    let P : ℕ := ∏ m in Finset.Icc 1 9, Nat.factorial m in
    let square_divisors : Finset ℕ := Finset.filter (λ s : ℕ => ∃ k : ℕ, s = k ^ 2) (Finset.divisors P) in
    Finset.card square_divisors = 672 := sorry

theorem infinite_m_exists : ∀ (k : ℕ), ∃ (m : ℕ), m > 0 ∧ k ≤ m ∧ ∃ (n : ℕ), n > 0 ∧ m * n ≤ m + n := sorry

theorem complex_identity : I = (1/5 : ℂ) + (3/5 : ℂ) * Complex.I := by
  intro V Z I hV hZ hI
  have hV_def : V = (1 : ℂ) + Complex.I := hV
  have hZ_def : Z = (2 : ℂ) - Complex.I := hZ
  have hI_def : V = I * Z := hI
  show I = (1/5 : ℂ) + (3/5 : ℂ) * Complex.I
  sorry

theorem not_necessarily_n_gt_84 : ¬∀ (n : ℕ) (hn : n > 0), (1/2 + 1/3 + 1/7 + 1/(n : ℕ)) ∈ ℤ → n > 84 := sorry

theorem remainder_of_power : (5 : ℤ) ^ 30 % (7 : ℤ) = (1 : ℤ) := sorry

theorem find_n_from_gcd_lcm (n : ℕ) (h_gcd : Nat.gcd n 40 = 10) (h_lcm : Nat.lcm n 40 = 280) : n = 70 := sorry

theorem product_identity : 
    let n : ℕ := 7 in
    let P := ∏ k in Finset.range n, ((2 : ℕ) ^ (2 ^ k) + (3 : ℕ) ^ (2 ^ k)) in
    P = (3 : ℕ) ^ (2 ^ n) - (2 : ℕ) ^ (2 ^ n) := sorry

theorem product_abc_eq_one_thirty_two (a b c : ℝ) (P : ℝ → ℝ) (hP : ∀ x, P x = x^3 + a * x^2 + b * x + c) 
    (hroots : ∀ x, P x = 0 ↔ x = Real.cos (2 * π / 7) ∨ x = Real.cos (4 * π / 7) ∨ x = Real.cos (6 * π / 7)) : 
    a * b * c = 1/32 := sorry

theorem arithmetic_progression_sum : 
    ∀ (a : ℕ → ℝ) (d : ℝ), (∀ (k : ℕ), a (k + 1) = a k + d) → d = 1 → 
    let n : ℕ := 98 in 
    (∑ k in Finset.range n, a (k + 1)) = 137 → (∑ k in Finset.range 49, a (2 * (k + 1))) = 93 := sorry

theorem line_intersection_sum_eq_four (x y : ℝ) (h₁ : 3 * y = x) (h₂ : 2 * x + 5 * y = 11) : x + y = 4 := sorry

theorem prime_divides_a_pow_p_minus_a (p : ℕ) (hp : Nat.Prime p) (a : ℕ) (ha : a > 0) : p ∣ a ^ p - a := sorry

theorem f_property (f : ℚ → ℝ) (h1 : ∀ (a b : ℚ), 0 < a → 0 < b → f (a * b) = f a + f b) (h2 : ∀ (p : ℕ), Nat.Prime p → f (p : ℚ) = (p : ℝ)) (x : ℚ) (hx : 0 < x) : f (25/11 : ℚ) < 0 := sorry

theorem sqrt_equation_implies_a_eq_eight (a : ℝ) :
    Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 → a = 8 := sorry

theorem inequality_proof (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : a * b + (a - b) ≤ 1 := sorry

theorem floor_sum_equals_3702 : 
    let N : ℝ := 1/3 in
    Int.floor (10 * N) + Int.floor (100 * N) + Int.floor (1000 * N) + Int.floor (10000 * N) = 3702 := sorry

theorem sum_inequality (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) :
    (a^2 / b + b^2 / c + c^2 / d + d^2 / a) ≥ (a + b + c + d) := sorry

theorem units_digit_product_eq_eight : 
    let a := (16^17 : ℕ) % 10 in
    let b := (17^18 : ℕ) % 10 in
    let c := (18^19 : ℕ) % 10 in
    (a * b * c) % 10 = 8 := sorry

theorem equation_solutions : ∃! (x : ℝ), x ∈ Set.Icc (0 : ℝ) π ∧ Real.sin ((π / 2) * Real.cos x) = Real.cos ((π / 2) * Real.sin x) := sorry

theorem maximum_value_of_f : 
    ∃ (t : ℝ), (fun (t : ℝ) => ((Real.rpow 2 t - 3 * t) * t) / (Real.rpow 4 t)) t = 1/12 ∧ 
    ∀ (x : ℝ), (fun (t : ℝ) => ((Real.rpow 2 t - 3 * t) * t) / (Real.rpow 4 t)) x ≤ 1/12 := sorry

theorem min_value_at_seven : ∀ (x : ℝ), x^2 - 14*x + 3 ≥ (7 : ℝ)^2 - 14*(7 : ℝ) + 3 := sorry

theorem sum_bound : ∀ (I M O : ℕ), I > 0 → M > 0 → O > 0 → I ≠ M → I ≠ O → M ≠ O → I * M * O = 2001 → I + M + O ≤ 671 := sorry

theorem number_of_solutions : 
    let I : Set ℝ := {x | 0 ≤ x ∧ x ≤ 2 * π} in
    let f : ℝ → ℝ := λ x => Real.tan (2 * x) - Real.cos (x / 2) in
    Finset.card (Finset.filter (λ x => f x = 0) (Set.toFinite I).toFinset) = 5 := sorry

theorem min_sum_gcd_lcm_constrained (m n : ℕ) (hm : m > 0) (hn : n > 0) (hgcd : Nat.gcd m n = 8) (hlcm : Nat.lcm m n = 112) : 
    ∃ (k : ℕ), m + n = k ∧ ∀ (m' n' : ℕ), m' > 0 → n' > 0 → Nat.gcd m' n' = 8 → Nat.lcm m' n' = 112 → k ≤ m' + n' := sorry

theorem sum_last_three_digits_of_5_pow_100_eq_13 : 
    let S := (5^100 % 1000).digits.sum in S = 13 := sorry

theorem sequence_mod_pattern : 
    let D : ℕ → ℤ := fun
      | 0 => 0
      | 1 => 0
      | 2 => 1
      | n + 3 => D (n + 2) + D n
    in (D 2021 % 2, D 2022 % 2, D 2023 % 2) = (0, 1, 0) := sorry

theorem root_bound (n : ℕ) (hn : n > 0) : (n : ℝ) ^ ((1 : ℝ) / (n : ℝ)) ≤ (2 : ℝ) - (1 : ℝ) / (n : ℝ) := sorry

theorem product_abc_eq_720 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a * (b + c) = 152) (h2 : b * (c + a) = 162) (h3 : c * (a + b) = 170) :
    a * b * c = 720 := sorry

theorem remainder_computation : let n : ℤ := 1529; let m : ℤ := 6 in n % m = 5 := sorry

theorem square_of_ninety_one : (91 : ℕ)^2 = 8281 := sorry

theorem log_base_3_of_27_eq_3 : Real.logb 3 (27 : ℝ) = (3 : ℝ) := sorry

theorem eq_neg_two_of_expr_eq_one (a : ℝ) (h : (8⁻¹ / 4⁻¹) - a⁻¹ = 1) : a = -2 := sorry

theorem complex_equation_implies_sum : ∀ (z : ℂ), 12 * ‖z‖^2 = 2 * ‖z + 2‖^2 + ‖z^2 + 1‖^2 + 31 → z + (6 : ℂ) / z = -2 := sorry

theorem arithmetic_geometric_means_square_sum :
    ∀ (x y : ℝ), (x + y) / 2 = 7 → Real.sqrt (x * y) = Real.sqrt 19 → x ^ 2 + y ^ 2 = 158 := sorry

theorem cube_root_equation : ∀ (r : ℝ), (r ^ (1/3 : ℝ) + 1 / (r ^ (1/3 : ℝ)) = 3) → (r ^ 3 + 1 / (r ^ 3) = 5778) := sorry

theorem exists_unique_initial_value : ∃! (x₁ : ℝ), ∀ (n : ℕ), 0 < x₁ ∧ let x := Nat.rec x₁ (λ k x_k => x_k * (x_k + (1 : ℝ)/(k : ℝ))) in 0 < x ∧ x < (Nat.rec x₁ (λ k x_k => x_k * (x_k + (1 : ℝ)/(k : ℝ))) (n + 1)) ∧ (Nat.rec x₁ (λ k x_k => x_k * (x_k + (1 : ℝ)/(k : ℝ))) (n + 1)) < 1 := sorry

theorem complex_set_max_distance :
    ∃ (A B : Set ℂ) (hA : ∀ z ∈ A, z ^ 3 - 8 = 0) (hB : ∀ z ∈ B, z ^ 3 - 8 * z ^ 2 - 8 * z + 64 = 0),
    (⨆ (a : A) (b : B), ‖(a : ℂ) - (b : ℂ)‖) = 2 * Real.sqrt 21 := sorry

theorem divides_power_plus_one (n : ℕ) : 11 ∣ (10 ^ n - (-1 : ℤ) ^ n) := sorry

theorem product_bound (n : ℕ) (a : ℕ → ℝ) (h_nonneg : ∀ i, 0 ≤ a i) (h_sum : ∑ i in Finset.range n, a i = n) :
    ∏ i in Finset.range n, a i ≤ 1 := sorry

theorem log_equation_solution :
    ∀ (x y : ℝ), 0 < x → x ≠ 1 → 0 < y → y ≠ 1 → Real.logb 2 x = Real.logb y 16 → x * y = 64 → (Real.logb 2 (x / y)) ^ 2 = 20 := sorry

theorem solve_for_c : ∀ (c : ℝ) (f : ℝ → ℝ), (∀ (x : ℝ), f x = c * x ^ 3 - 9 * x + 3) → f 2 = 9 → c = 3 := sorry

theorem inequality_proof (x : ℝ) (n : ℕ) (hx : x > -1) : (1 + (n : ℝ) * x) ≤ (1 + x) ^ n := sorry

theorem remainder_condition (n : ℤ) (a : ℤ := (123456 : ℤ)) (m : ℤ := (101 : ℤ)) :
    0 ≤ n ∧ n < 101 ∧ a % m = n % m ∧ n = 34 := sorry

theorem son_age_solution (f s : ℕ) (h1 : f = 5 * s) (h2 : (f - 3) + (s - 3) = 30) : s = 6 := sorry

theorem arithmetic_series_solution (a d : ℝ) : 
    (let S_n : ℕ → ℝ := λ n => (n : ℝ) / 2 * (2 * a + ((n : ℝ) - 1) * d)
    in S_n 5 = 70 ∧ S_n 10 = 210) → a = 42/5 := sorry

theorem product_mod_eq : (121 : ℤ) * 122 * 123 % 4 = 2 := sorry

theorem sum_mod_eq : (∑ k in Finset.Icc 1 12, k) % 4 = 2 := sorry

theorem expression_equals_eleven : 
    let x : ℝ := 4 in (3*x - 2)*(4*x + 1) - (3*x - 2)*4*x + 1 = 11 := sorry

theorem sum_of_absolute_value_condition : 
    let S : Set ℝ := {x | |2 - x| = 3} in 
    ∑ x in S, x = 4 := sorry

theorem product_of_roots_eq_20 : ∀ (x : ℝ), (x^2 + 18*x + 30 = 2 * Real.sqrt (x^2 + 18*x + 45)) → 
    ∃ (r1 r2 : ℝ), (∀ (r : ℝ), (r = r1 ∨ r = r2) ↔ (r^2 + 18*r + 30 = 2 * Real.sqrt (r^2 + 18*r + 45))) ∧ r1 * r2 = 20 := sorry

theorem f_of_three_eq_eight (a b : ℝ) (f : ℝ → ℝ) (h : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5) (h2 : f (-3) = 2) : f 3 = 8 := sorry

theorem solve_problem : ∃ (a b c d : ℕ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a * b * c * d = 40320 ∧ a * b + a + b = 524 ∧ b * c + b + c = 146 ∧ c * d + c + d = 104 ∧ a - d = 10 := sorry

theorem base3_1222_to_base10_eq_53 : (Nat.ofDigits 3 [1, 2, 2, 2] : ℤ) = (53 : ℤ) := sorry

theorem remainder_equality (n : ℕ) (hn : n > 0) : (3^(2^n) - 1) % (2^(n + 3)) = (2^(n + 2)) % (2^(n + 3)) := sorry

theorem arithmetic_sequence_problem (a d : ℝ) (T : ℕ → ℝ) (hT_def : ∀ n, T n = a + ((n : ℝ) - 1) * d) (hT7 : T 7 = 30) (hT11 : T 11 = 60) : T 21 = 135 := sorry

theorem f_value_at_84 : f (84 : ℤ) = (997 : ℤ) := sorry

theorem functional_equation_solutions : 
    {f : ℤ → ℤ | ∀ (a b : ℤ), f (2 * a) + 2 * f b = f (f (a + b))} = {f | f = fun _ => 0} ∪ {f | f = fun x => x} ∪ {f | f = fun x => -x} := sorry

theorem composition_result : f (g (2 : ℝ)) = (8 : ℝ) := sorry

theorem ordered_pair_equals_one_one (a b : ℝ) (h1 : 3 * a + 2 * b = 5) (h2 : a + b = 2) : (a, b) = (1, 1) := sorry

theorem prime_product_minus_sum_eq_119 : ∃ (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q), 
    p ∈ ({5, 7, 11, 13, 17} : Set ℕ) ∧ q ∈ ({5, 7, 11, 13, 17} : Set ℕ) ∧ p ≠ q ∧ (p * q - (p + q)) = 119 := sorry

theorem remainder_of_sum_mod_10 : (239 + 174 + 83) % 10 = 6 := sorry

theorem problem_statement : ∀ (f : ℕ × ℕ → ℕ) (h1 : ∀ x y, 0 < x → 0 < y → 0 < f (x, y)) (h2 : ∀ x > 0, f (x, x) = x) (h3 : ∀ x y, 0 < x → 0 < y → f (x, y) = f (y, x)) (h4 : ∀ x y, 0 < x → 0 < y → (x + y) * f (x, y) = y * f (x, x + y)), f (14, 52) = 364 := sorry

theorem cube_root_expression_eq_four : ((16 * (Real.rpow (a ^ 2) (1/3 : ℝ))) ^ (1/3 : ℝ)) = 4 := by
  intro a (ha : a = (8 : ℝ))
  rw [ha]
  sorry

theorem product_of_square_roots (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := sorry

theorem water_consumption (d w : ℝ) (h : w = 1.5 * (d / 3)) : d = 10 → w = 5 := sorry

theorem number_of_zeros : 
    let f (θ : ℝ) : ℝ := 1 - 3 * Real.sin θ + 5 * Real.cos (3 * θ) in
    Finset.card (Finset.filter (λ θ => f θ = 0) (Set.toFinset (Set.Ioo (0 : ℝ) (2 * π)))) = 6 := sorry

theorem log_sqrt_identity (a b c x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    Real.sqrt (Real.logb 2 6 + Real.logb 3 6) = Real.sqrt (Real.logb 2 3) + Real.sqrt (Real.logb 3 2) := sorry

theorem inequality_power_mean : ∀ (a : ℝ) (b : ℝ) (n : ℕ), a > 0 → b > 0 → n > 0 → ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := sorry

theorem sum_power_identity (a b x y : ℝ) (h1 : a * x + b * y = 3) (h2 : a * x^2 + b * y^2 = 7) (h3 : a * x^3 + b * y^3 = 16) (h4 : a * x^4 + b * y^4 = 42) : a * x^5 + b * y^5 = 20 := sorry

theorem periodic_function_exists (a : ℝ) (ha : a > 0) (f : ℝ → ℝ) 
    (hf : ∀ x : ℝ, f (x + a) = 1/2 + Real.sqrt (f x - (f x)^2)) : 
    ∃ (b : ℝ), b > 0 ∧ ∀ x : ℝ, f (x + b) = f x := sorry

theorem remainder_equals_two : u = 2 := sorry

theorem remainder_of_194_div_11 : 194 % 11 = 7 := sorry

theorem inequality_bounds (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : a + b + c = 2) (h4 : a * b + b * c + c * a = 1) : 0 ≤ a ∧ a ≤ 1/3 := sorry

theorem count_integers_with_absolute_value_less_than_three_pi : 
    Finset.card (Finset.filter (λ (x : ℤ) => |(x : ℝ)| < 3 * π) Finset.univ) = 19 := sorry

theorem absolute_difference_eq : 
    ∀ (a b : ℕ), a + b = 17402 → 10 ∣ a → a % 10 = 0 → a / 10 = b → |(a : ℤ) - (b : ℤ)| = 14238 := sorry

theorem sequence_problem (a b : ℕ → ℝ) (h_rec : ∀ n, (a (n + 1), b (n + 1)) = (Real.sqrt 3 * a n - b n, Real.sqrt 3 * b n + a n)) (h_final : (a 100, b 100) = (2, 4)) : a 1 + b 1 = 1 / ((2 : ℝ) ^ 98) := sorry

theorem prime_sum_equation (m n : ℕ) (hm : Nat.Prime m) (hn : Nat.Prime n) (k t : ℕ) (hk : k > 0) (ht : t > 0) (hkt : k > t) 
    (hroots : ∀ x : ℕ, x > 0 → (x^2 - m * x + n = 0 ↔ x = k ∨ x = t)) : 
    m ^ n + n ^ m + k ^ t + t ^ k = 20 := sorry

theorem even_product_implies_second_is_eighteen (n : ℕ) (h : (2 * n) * (2 * n + 2) = 288) : 2 * n + 2 = 18 := sorry

theorem sum_equals_sqrt_five (a : ℝ) (b : ℝ) (ha_pos : a > 0) (hb_pos : b > 0) (h_ne : a ≠ b) 
    (h_a : |a - 1/a| = 1) (h_b : |b - 1/b| = 1) : a + b = Real.sqrt 5 := sorry

theorem triangle_inequality_expression (a : ℝ) (b : ℝ) (c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) 
    (h1 : a + b > c) (h2 : b + c > a) (h3 : c + a > b) : 
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := sorry

theorem polynomial_coefficient_B :
    ∀ (A B C D : ℤ) (r1 r2 r3 r4 r5 r6 : ℕ) (hpos : r1 > 0 ∧ r2 > 0 ∧ r3 > 0 ∧ r4 > 0 ∧ r5 > 0 ∧ r6 > 0),
    (∀ (z : ℂ), z ^ 6 - 10 * z ^ 5 + A * z ^ 4 + B * z ^ 3 + C * z ^ 2 + D * z + 16 = 
        (z - (r1 : ℂ)) * (z - (r2 : ℂ)) * (z - (r3 : ℂ)) * (z - (r4 : ℂ)) * (z - (r5 : ℂ)) * (z - (r6 : ℂ))) →
    B = -88 := sorry

theorem solve_system (a b : ℝ) (h1 : a ^ 2 * b ^ 3 = (32 : ℝ)/27) (h2 : a / b ^ 3 = (27 : ℝ)/4) : a + b = (8 : ℝ)/3 := sorry

theorem arithmetic_sequence_nth_term : 
    ∀ (x d : ℝ) (a₁ : ℝ) (h₁ : a₁ = 2*x - 3) (a₂ : ℝ) (h₂ : a₂ = 5*x - 11) (a₃ : ℝ) (h₃ : a₃ = 3*x + 1) 
    (h_arithmetic : a₂ - a₁ = a₃ - a₂) (n : ℕ) (a_n : ℝ) (h_nth : a_n = a₁ + (n : ℝ) * d) (h_a_n : a_n = 2009), 
    n = 502 := sorry

