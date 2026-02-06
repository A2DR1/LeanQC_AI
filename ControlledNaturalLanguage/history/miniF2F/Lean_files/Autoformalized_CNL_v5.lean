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


theorem odd_positive_integers_with_conditions (a b c d k m : ℤ) (ha_odd : Odd a) (hb_odd : Odd b) (hc_odd : Odd c) (hd_odd : Odd d) (ha_pos : a > 0) (hb_pos : b > 0) (hc_pos : c > 0) (hd_pos : d > 0) (hab : a < b) (hbc : b < c) (hcd : c < d) (had_eq : a * d = b * c) (h_sum1 : a + d = 2 ^ k) (h_sum2 : b + c = 2 ^ m) : a = 1 := sorry

theorem abs_sum_inequality (a b : ℝ) : |a + b| / (1 + |a + b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := sorry

theorem multiplicative_inverse_modulo : ∀ (n : ℤ), 0 ≤ n → n < 1399 → n = 1058 := sorry

theorem not_prime_product (K L M N : ℤ) (hKgtL : K > L) (hLgtM : L > M) (hMgtN : M > N) (hKpos : K > 0) (hLpos : L > 0) (hMpos : M > 0) (hNpos : N > 0) (h_eq : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) : ¬ Nat.Prime (K * L + M * N) := sorry

theorem inequality_proof (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := sorry

theorem mod_problem (n : ℤ) (h : 2 * n ≡ 15 [ZMOD 47]) : n ≡ 31 [ZMOD 47] := sorry

theorem mod_goal (b : ℤ) (h1 : 0 ≤ b) (h2 : b ≤ 120) : 24 * b ≡ 1 [ZMOD 121] := sorry

theorem solve_system : ∀ (x y z : ℝ), 3 * x + y = 17 → 5 * y + z = 14 → 3 * x + 5 * z = 41 → x + y + z = 12 := sorry

theorem function_composition_result : f (f (f (f (f (4 : ℤ))))) = (1 : ℤ) := sorry

theorem perfect_square_div (n : ℤ) (hn : n ≥ 9) (hn_fact : (Nat.factorial (Int.natAbs n)) ≠ 0) :
    ∃ (k : ℤ), ((Nat.factorial (Int.natAbs (n + 2))) - (Nat.factorial (Int.natAbs (n + 1)))) / (Nat.factorial (Int.natAbs n)) = k ^ 2 := sorry

theorem irrational_power_rational (a b : ℝ) (ha : Irrational a) (hb : Irrational b) : ∃ (q : ℚ), (a : ℝ) ^ (b : ℝ) = (q : ℝ) := sorry

theorem gcd_conditions : ∃ (k : ℤ), 0 < k ∧ (∀ (n : ℤ), 0 < n →
    let a := 6 * n + k; b := 6 * n + 3; c := 6 * n + 2; d := 6 * n + 1 in
    Int.gcd a b = 1 ∧ Int.gcd a c = 1 ∧ Int.gcd a d = 1) ∧
    (∀ (k' : ℤ), 0 < k' ∧ k' < k → ¬ ∀ (n : ℤ), 0 < n →
    let a := 6 * n + k'; b := 6 * n + 3; c := 6 * n + 2; d := 6 * n + 1 in
    Int.gcd a b = 1 ∧ Int.gcd a c = 1 ∧ Int.gcd a d = 1) := sorry

theorem count_four_digit_multiples_of_five_with_even_nonzero_digits :
    Finset.card (Finset.filter (λ (n : ℕ) =>
      ∃ (d1 d2 d3 d4 : ℕ),
        n > 0 ∧ n ≥ 1000 ∧ n ≤ 9999 ∧ n % 5 = 0 ∧
        d1 % 2 = 0 ∧ d2 % 2 = 0 ∧ d3 % 2 = 0 ∧ d4 % 2 = 0 ∧
        d1 ≥ 0 ∧ d2 ≥ 0 ∧ d3 ≥ 0 ∧ d4 ≥ 0 ∧
        d1 ≤ 9 ∧ d2 ≤ 9 ∧ d3 ≤ 9 ∧ d4 ≤ 9 ∧
        d1 ≠ 0 ∧
        n = 1000 * d1 + 100 * d2 + 10 * d3 + d4)
      (Finset.Icc 1 9999)) = 100 := sorry

theorem log_sum_product_eq_21000 :
    let S1 := ∑ k in Finset.Icc (1 : ℤ) 20, Real.logb ((5 : ℝ)^(k : ℤ)) ((3 : ℝ)^((k : ℤ)^2)) in
    let S2 := ∑ k in Finset.Icc (1 : ℤ) 100, Real.logb ((9 : ℝ)^(k : ℤ)) ((25 : ℝ)^(k : ℤ)) in
    S1 * S2 = (21000 : ℝ) := sorry

theorem sum_sqrt_bound : ∃ (k : ℤ) (h : k ≥ 2) (S : ℝ), S = ∑ k in Finset.Icc (2 : ℤ) 10000, (1 : ℝ) / Real.sqrt (k : ℝ) ∧ (∀ (k : ℤ), k > 0) → S < 198 := sorry

theorem theorem_statement : ∀ (n : ℤ) (hn : n > 0) (p : ℤ → ℤ) (hp : ∀ k, p k = k ^ 2 - k + 41) (a b : ℤ) (ha : a = p n) (hb : b = p (n + 1)) (d : ℤ) (hd : d > 1) (hda : d ∣ a) (hdb : d ∣ b), n = 41 := sorry

theorem integer_factorization_identity (A B : ℤ) (x : ℝ) (h : 10 * x ^ 2 - x - 24 = (A * x - 8) * (B * x + 3)) : A * B + B = 12 := sorry

theorem inequality_proof (a b : ℝ) (ha : a > 0) (hb : b > 0) (hle : b ≤ a) : (a + b)/2 - Real.sqrt (a * b) ≤ (a - b)^2/(8 * b) := sorry

theorem cardinality_of_A_is_672 :
    let P : ℤ := ∏ i in Finset.Icc 1 9, ∏ j in Finset.Icc 1 i, j in
    let A : Set ℤ := {s | s > 0 ∧ s^2 ∣ P} in
    Finset.card (A ∩ Finset.Icc 1 P).toFinset = 672 := sorry

theorem infinitely_many_m_with_n_satisfying_inequality : ∀ (k : ℤ), ∃ (m : ℤ), m > k ∧ ∃ (n : ℤ), n > 0 ∧ m * n ≤ m + n := sorry

theorem complex_equation : ∀ (V I Z : ℂ), V = (1 : ℂ) + Complex.I → Z = (2 : ℂ) - Complex.I → Z ≠ 0 → I = (1/5 : ℂ) + (3/5 : ℂ) * Complex.I := sorry

theorem not_n_gt_84 : ∀ (n : ℤ) (hpos : n > 0) (hne_zero : n ≠ 0) (S : ℝ) (hS_sum : S = (1/2 : ℝ) + (1/3 : ℝ) + (1/7 : ℝ) + (1 / (n : ℝ))) (hS_int : S ∈ ℤ), ¬(n > 84) := sorry

theorem remainder_theorem : ∀ (n : ℤ), n = 30 → ∀ (a : ℤ), a = 5 → ∀ (b : ℤ), b = 7 → b ≠ 0 → a ^ n % b = 1 := sorry

theorem problem_statement : ∀ (n : ℤ), n > 0 → ∀ (d : ℤ), d = gcd n 40 → d = 10 → ∀ (l : ℤ), l = lcm n 40 → l = 280 → n = 70 := sorry

theorem product_identity :
    let a : ℕ := 2
    let b : ℕ := 3
    let P : ℕ := ∏ k in Finset.range 7, (a^(2^k) + b^(2^k)) in
    P = b^128 - a^128 := sorry

theorem cubic_identity (a b c : ℝ) (P : ℝ → ℝ) (hP : ∀ x, P x = x^3 + a * x^2 + b * x + c) (r1 r2 r3 : ℝ)
    (hr1 : r1 = Real.cos (2 * π / 7)) (hr2 : r2 = Real.cos (4 * π / 7)) (hr3 : r3 = Real.cos (6 * π / 7))
    (hroots : ∀ x, P x = 0 ↔ x = r1 ∨ x = r2 ∨ x = r3) : a * b * c = 1/32 := sorry

theorem sequence_sum_goal : ∀ (a : ℕ → ℝ) (h_seq : ∀ (n : ℕ), a (n + 1) = a n + 1) (S : ℝ) (h_S_eq : S = 137) (h_sum : S = ∑ k in Finset.Icc 1 98, a k), ∑ k in Finset.Icc 1 49, a (2 * k) = 93 := sorry

theorem solve_system (x y : ℝ) (h1 : 3 * y = x) (h2 : 2 * x + 5 * y = 11) : x + y = 4 :=
  sorry

theorem prime_divides_a_pow_p_minus_a (p : ℕ) (hp : Nat.Prime p) (a : ℤ) (ha : a > 0) : (p : ℤ) ∣ a ^ p - a := sorry

theorem f_inequality : f (25/11 : ℚ) < 0 := sorry

theorem sqrt_equation_implies_a_eq_8 (a : ℝ) (h1 : 16 + 16 * a ≥ 0) (h2 : 1 + a ≥ 0) (h3 : 4 + Real.sqrt (16 + 16 * a) ≥ 0) (h4 : 1 + Real.sqrt (1 + a) ≥ 0) : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6 → a = 8 := sorry

theorem inequality_proof (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : a * b + (a - b) ≤ 1 := sorry

theorem floor_sum_eq_3702 (N : ℝ) (hN : N = 1/3) (h3 : (3 : ℝ) ≠ 0) :
    ⌊10 * N⌋ + ⌊100 * N⌋ + ⌊1000 * N⌋ + ⌊10000 * N⌋ = 3702 := sorry

theorem inequality_proof (a b c d : ℝ) (ha_pos : a > 0) (hb_pos : b > 0) (hc_pos : c > 0) (hd_pos : d > 0)
  (hb_ne_zero : b ≠ 0) (hc_ne_zero : c ≠ 0) (hd_ne_zero : d ≠ 0) (ha_ne_zero : a ≠ 0) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := sorry

theorem units_digit_product_eq_8 :
    let n : ℤ := 16; m : ℤ := 17; k : ℤ := 18; a : ℤ := 17; b : ℤ := 18; c : ℤ := 19 in
    n > 0 → m > 0 → k > 0 → a > 0 → b > 0 → c > 0 →
    ((n ^ a) * (m ^ b) * (k ^ c)) % 10 = 8 := sorry

theorem count_solutions_eq_two :
    let f : ℝ → ℝ := λ x => Real.sin ((π / 2) * Real.cos x)
    let g : ℝ → ℝ := λ x => Real.cos ((π / 2) * Real.sin x) in
    Finset.card (Finset.filter (λ x => f x = g x) (Set.Icc (0 : ℝ) π).toFinset) = 2 := sorry

theorem maximum_value_of_f :
    ∃ (t : ℝ), f t = 1/12 ∧ ∀ (x : ℝ), f x ≤ 1/12 := by
  sorry

theorem minimum_occurs_at_seven : ∀ (f : ℝ → ℝ), (∀ (x : ℝ), f x = x^2 - 14*x + 3) → IsMinOn f univ 7 := sorry

theorem maximum_sum_condition (I M O : ℤ) (hI : I > 0) (hM : M > 0) (hO : O > 0) (hIM : I ≠ M) (hMO : M ≠ O) (hIO : I ≠ O) (hprod : I * M * O = 2001) :
    I + M + O ≤ 671 := sorry

theorem count_solutions :
    let x : ℝ := x;
    let f : ℝ → ℝ := λ x => Real.tan (2 * x);
    let g : ℝ → ℝ := λ x => Real.cos (x / 2) in
    ∀ (hx1 : 0 ≤ x) (hx2 : x ≤ 2 * π) (hf : ∀ x, f x = Real.tan (2 * x)) (hg : ∀ x, g x = Real.cos (x / 2))
    (h1 : ∀ x, ¬∃ (k : ℤ), 2 * x = π / 2 + k * π) (h2 : ∀ x, ¬∃ (k : ℤ), 2 * x = -π / 2 + k * π),
    Finset.card (Finset.filter (λ x => f x = g x) (Finset.Icc (0 : ℝ) (2 * π))) = 5 := sorry

theorem min_sum_given_gcd_lcm :
    ∀ (m n : ℤ) (hm : m > 0) (hn : n > 0) (d : ℤ) (hd1 : d = gcd m n) (hd2 : d = 8)
    (l : ℤ) (hl1 : l = lcm m n) (hl2 : l = 112), 72 ≤ m + n := sorry

theorem sum_of_final_three_digits : ∃ (n : ℤ) (h : n = (100 : ℤ)) (S : ℤ), S = (5^n).toNat % 1000 / 100 + (5^n).toNat % 100 / 10 + (5^n).toNat % 10 ∧ S = 13 := sorry

theorem parity_pattern :
    let D : ℕ → ℤ := fun n =>
      match n with
      | 0 => 0
      | 1 => 0
      | 2 => 1
      | n + 3 => D (n + 2) + D n
      end in
    (Int.even (D 2021) ∧ ¬ Int.even (D 2022) ∧ Int.even (D 2023)) := sorry

theorem inequality_for_positive_n (n : ℕ) (h : n > 0) : (n : ℝ) ^ ((1 : ℝ) / (n : ℝ)) ≤ (2 : ℝ) - (1 : ℝ) / (n : ℝ) := sorry

theorem product_abc_eq_720 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a * (b + c) = 152) (h2 : b * (c + a) = 162) (h3 : c * (a + b) = 170) :
    a * b * c = 720 := sorry

theorem remainder_computation : ∀ (n m : ℤ), n = 1529 → m = 6 → m > 0 → n % m = 5 := sorry

theorem n_squared_eq_8281 : ∀ (n : ℤ), n = 91 → n ^ 2 = 8281 := sorry

theorem log_goal : ∀ (b : ℝ), b = Real.logb 3 27 → b = 3 := sorry

theorem inverse_equation_implies_a_equals_neg_two (a : ℝ) (h : a ≠ 0) : ((8⁻¹ : ℝ) / (4⁻¹ : ℝ)) - (a⁻¹) = 1 → a = -2 := sorry

theorem complex_equation (z : ℂ) (h : 12 * ‖z‖^2 = 2 * ‖z + 2‖^2 + ‖z^2 + 1‖^2 + 31) : z + (6 / z) = -2 := sorry

theorem arithmetic_geometric_relation (x y AM GM : ℝ) (hAM_eq : AM = 7) (hAM_formula : AM = (x + y) / 2)
    (hGM_eq : GM = Real.sqrt 19) (hGM_formula : GM = Real.sqrt (x * y)) (h_nonneg : x * y ≥ 0)
    (h_two_ne_zero : (2 : ℝ) ≠ 0) : x ^ 2 + y ^ 2 = 158 := sorry

theorem cube_sum_identity (r : ℝ) (h1 : r ≠ 0) (h2 : Real.rpow r (1/3 : ℝ) + 1 / Real.rpow r (1/3 : ℝ) = 3) : r ^ 3 + 1 / (r ^ 3) = 5778 := sorry

theorem exists_unique_initial_value : ∃! (x₁ : ℝ), ∀ (x : ℕ → ℝ) (n : ℤ), n > 0 → (∀ (k : ℕ), x (k + 1) = x k * (x k + (1 : ℝ) / (k : ℝ))) → (0 : ℤ) ≠ n → (∀ (m : ℕ), 0 < x m ∧ x m < x (m + 1) ∧ x (m + 1) < 1) := sorry

theorem complex_set_distance_eq :
    ∃ (A B : Set ℂ) (z : ℂ) (d : ℝ),
      A = {z : ℂ | z ^ 3 - 8 = 0} ∧
      B = {z : ℂ | z ^ 3 - 8 * z ^ 2 - 8 * z + 64 = 0} ∧
      d = sSup {x : ℝ | ∃ (a : ℂ) (b : ℂ), a ∈ A ∧ b ∈ B ∧ x = Complex.abs (a - b)} ∧
      d = 2 * Real.sqrt 21 := sorry

theorem divides_power_expression (n : ℕ) : 11 ∣ (10 ^ n - (-1 : ℤ) ^ n) := sorry

theorem product_bound (n : ℕ) (hn : n > 0) (a : ℕ → ℝ) (ha_nonneg : ∀ i, i ∈ Finset.Icc 1 n → a i ≥ 0) (ha_sum : ∑ i in Finset.Icc 1 n, a i = n) :
    ∏ i in Finset.Icc 1 n, a i ≤ 1 := sorry

theorem log_property (x y : ℝ) (hx_pos : x > 0) (hx_ne_one : x ≠ 1) (hy_pos : y > 0) (hy_ne_one : y ≠ 1)
    (h_log_eq : Real.logb 2 x = Real.logb y 16) (h_product : x * y = 64) :
    (Real.logb 2 (x / y)) ^ 2 = 20 := sorry

theorem solve_for_c : ∀ (f : ℝ → ℝ) (c : ℝ), (∀ x, f x = c * (x ^ 3) - 9 * x + 3) → f 2 = 9 → c = 3 := sorry

theorem inequality_proof (x : ℝ) (n : ℕ) (hx : x > -1) : (1 + (n : ℝ) * x) ≤ (1 + x) ^ n := sorry

theorem mod_problem : ∀ (n : ℤ), 0 ≤ n → n < 101 → (123456 ≡ n [ZMOD 101] → n = 34) := sorry

theorem solve_for_s (f s : ℤ) (hf_pos : f > 0) (hs_pos : s > 0) (h_eq : f = 5 * s) (h_sum : (f - 3) + (s - 3) = 30) : s = 6 := sorry

theorem arithmetic_sequence_sum :
    ∀ (n : ℤ) (h : n > 0) (S : ℕ → ℝ) (a d : ℝ)
    (hS : ∀ n, S n = (n : ℝ) / 2 * (2 * a + ((n : ℝ) - 1) * d))
    (hS5 : S 5 = 70) (hS10 : S 10 = 210) (h5 : (5 : ℕ) ≠ 0),
    a = 42/5 := sorry

theorem remainder_problem : ∃ (n m p : ℤ), n = 121 ∧ m = 122 ∧ p = 123 ∧ (n * m * p) % 4 = 2 := sorry

theorem sum_mod_four_eq_two (n : ℤ) (hn : n = (12 : ℤ)) (S : ℤ) (hS : S = ∑ k in Finset.Icc (1 : ℤ) n, k) : S % 4 = 2 := sorry

theorem real_equation : ∀ (x : ℝ), x = 4 → (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * 4 * x + 1 = 11 := sorry

theorem sum_of_solutions_eq_four : ∃ (x : ℝ), |2 - x| = 3 ∧ (∀ (y : ℝ), |2 - y| = 3 → y = x) → (let solutions := {z : ℝ | |2 - z| = 3} in ∑ z in solutions, z = 4) := sorry

theorem product_of_roots_eq_20 : ∀ (x a b r1 r2 : ℝ), a = x ^ 2 + 18 * x + 30 → b = x ^ 2 + 18 * x + 45 → a = 2 * Real.sqrt b → b ≥ 0 → r1 ^ 2 + 18 * r1 + 30 = 2 * Real.sqrt (r1 ^ 2 + 18 * r1 + 45) → r2 ^ 2 + 18 * r2 + 30 = 2 * Real.sqrt (r2 ^ 2 + 18 * r2 + 45) → r1 ≠ r2 → r1 * r2 = 20 := sorry

theorem f_of_three_eq_eight (a b : ℝ) (f : ℝ → ℝ) (h1 : ∀ x, f x = a * (x ^ 4) - b * (x ^ 2) + x + 5) (h2 : f (-3) = 2) : f 3 = 8 := sorry

theorem integer_solution : ∀ (a b c d : ℤ), a > 0 → b > 0 → c > 0 → d > 0 → a * b * c * d = 40320 → a * b + a + b = 524 → b * c + b + c = 146 → c * d + c + d = 104 → a - d = 10 := sorry

theorem base_three_value : ∃ (n : ℤ) (h : n > 0) (a b c d : ℤ) (ha : a = 1) (hb : b = 2) (hc : c = 2) (hd : d = 2) (base : ℤ) (hbase_eq : base = 3) (hbase_ne_zero : base ≠ 0) (number_in_base_three : ℕ → ℤ) (h0 : number_in_base_three 0 = a) (h1 : number_in_base_three 1 = b) (h2 : number_in_base_three 2 = c) (h3 : number_in_base_three 3 = d) (value_in_base_ten : ℤ) (hvalue : value_in_base_ten = (a * (base ^ 3)) + (b * (base ^ 2)) + (c * (base ^ 1)) + (d * (base ^ 0))), value_in_base_ten = 53 := sorry

theorem remainder_theorem (n : ℤ) (hn : n > 0) : (3^(2^n) - 1) % (2^(n + 3)) = 2^(n + 2) := sorry

theorem arithmetic_sequence_problem : a_21 = 135 := sorry

theorem f_84_eq_997 : f 84 = 997 := sorry

theorem determine_functions :
    {f : ℤ → ℤ | ∀ (a b : ℤ), f (2 * a) + 2 * f b = f (f (a + b))} = {f | f = fun _ => 0} ∪ {f | f = fun x => x} ∪ {f | f = fun x => -x} := sorry

theorem function_composition_example : f (g 2) = 8 := by
  intro f g
  intro hf : ∀ x, f x = x + 1
  intro hg : ∀ x, g x = x ^ 2 + 3
  rw [hg]
  rw [hf]
  ring
  done

theorem ordered_pair_equality (a b : ℝ) (h1 : 3 * a + 2 * b = 5) (h2 : a + b = 2) : (a, b) = (1, 1) := sorry

theorem prime_sum_product_difference_eq_119 : ∃ (p q : ℤ) (hp : Nat.Prime (Int.natAbs p)) (hq : Nat.Prime (Int.natAbs q)) (hp_gt : p > (4 : ℤ)) (hp_lt : p < (18 : ℤ)) (hq_gt : q > (4 : ℤ)) (hq_lt : q < (18 : ℤ)) (hne : p ≠ q), ∀ (s r d : ℤ) (hs : s = p + q) (hr : r = p * q) (hd : d = r - s), d = (119 : ℤ) := sorry

theorem r_eq_6 : r = 6 := by
  intro S (hS : S = (239 : ℤ)) W (hW : W = (174 : ℤ)) Z (hZ : Z = (83 : ℤ)) T (hT : T = S + W + Z) r (hr : r = T % (10 : ℤ))
  rw [hS, hW, hZ] at hT
  rw [hT] at hr
  rw [hr]
  native_decide

theorem f_14_52_eq_364 : f (14 : ℤ) (52 : ℤ) = (364 : ℤ) := sorry

theorem cube_root_property (a : ℝ) (h1 : a = 8) (h2 : a ≥ 0) : (16 * ((a ^ 2) ^ (1/3 : ℝ))) ^ (1/3 : ℝ) = 4 := sorry

theorem radical_simplification (x : ℝ) (hx : x ≥ 0) : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * Real.sqrt (35) * x := sorry

theorem goal_statement : w = 5 := by
  intro d hd m1 hm1 m2 hm2 hm1_ne_zero r hr w hw
  rw [hw, hr, hd, hm1, hm2]
  norm_num

theorem count_roots : Finset.card (Finset.filter (λ θ : ℝ => f θ = 0) (Set.toFinset (Set.Ioo (0 : ℝ) (2 * π)))) = 6 := sorry

theorem log_sqrt_equality : a = b := by
  intro a (ha : a = Real.sqrt (Real.logb 2 6 + Real.logb 3 6))
  intro b (hb : b = Real.sqrt (Real.logb 2 3) + Real.sqrt (Real.logb 3 2))
  rw [ha, hb]
  sorry

theorem power_mean_inequality (a b : ℝ) (n : ℤ) (ha : a > 0) (hb : b > 0) (hn : n > 0) : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := sorry

theorem linear_combination_identity (a b x y : ℝ) (h1 : a * x + b * y = 3) (h2 : a * x^2 + b * y^2 = 7)
    (h3 : a * x^3 + b * y^3 = 16) (h4 : a * x^4 + b * y^4 = 42) : a * x^5 + b * y^5 = 20 := sorry

theorem periodic_function_exists (a : ℝ) (h : a > 0) (f : ℝ → ℝ)
    (h1 : ∀ x, f (x + a) = 1/2 + Real.sqrt (f x - (f x)^2))
    (h2 : ∀ x, f x - (f x)^2 ≥ 0) :
    ∃ b > 0, ∀ x, f (x + b) = f x := sorry

theorem units_digit_eq_two : ∃ (n : ℤ), n = 29 * 79 + 31 * 81 ∧ n % 10 = 2 := sorry

theorem remainder_computation : ∀ (n m : ℤ), n = 194 → m = 11 → m ≠ 0 → n % m = 7 := sorry

theorem inequality_bounds (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : a + b + c = 2) (h4 : a * b + b * c + c * a = 1) :
    0 ≤ a ∧ a ≤ 1/3 ∧ 1/3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4/3 := sorry

theorem integer_values_count : ∀ (π : ℤ) (hπ : π > 0), Finset.card (Finset.filter (λ x : ℤ => |x| < 3 * π) Finset.univ) = 6 * π - 1 := sorry

theorem compute_absolute_difference (x y : ℕ) (h_sum : x + y = 17402) (h_div : ∃ (k : ℕ), x = 10 * k) (h_units_erased : y = x / 10) : |(x : ℤ) - (y : ℤ)| = 15462 := sorry

theorem sequence_problem (n : ℤ) (hn : n > 0) (a b : ℕ → ℝ)
    (ha : ∀ n, a (n + 1) = Real.sqrt 3 * a n - b n)
    (hb : ∀ n, b (n + 1) = Real.sqrt 3 * b n + a n)
    (h100a : a 100 = 2) (h100b : b 100 = 4) :
    a 1 + b 1 = 1 / ((2 : ℝ) ^ 98) := sorry

theorem prime_sum_equation (m n k t : ℤ) (x : ℝ) (hm_pos : m > 0) (hn_pos : n > 0) (hk_pos : k > 0) (ht_pos : t > 0)
    (hk_gt_t : k > t) (hm_prime : Nat.Prime m) (hn_prime : Nat.Prime n) (hx_eq : x^2 - (m : ℝ) * x + (n : ℝ) = 0)
    (h_solutions : {s : ℕ | s > 0 ∧ ((s : ℝ)^2 - (m : ℝ) * (s : ℝ) + (n : ℝ) = 0)} = ({k, t} : Set ℕ)) :
    (m : ℝ)^(n : ℝ) + (n : ℝ)^(m : ℝ) + (k : ℝ)^(t : ℝ) + (t : ℝ)^(k : ℝ) = 20 := sorry

theorem solve_equation : ∀ (n : ℤ), n > 0 → ∀ (a : ℤ), a = 2 * n → ∀ (b : ℤ), b = a + 2 → a * b = 288 → b = 18 := sorry

theorem real_sum_condition (a b : ℝ) (ha_pos : a > 0) (hb_pos : b > 0) (h_ne : a ≠ b)
    (ha_eq : a - (1 / a) = 1) (ha_div_ne_zero : 1 / a ≠ 0)
    (hb_eq : b - (1 / b) = 1) (hb_div_ne_zero : 1 / b ≠ 0) :
    a + b = Real.sqrt 5 := sorry

theorem inequality_theorem (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h1 : a + b > c) (h2 : b + c > a) (h3 : c + a > b) :
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := sorry

theorem polynomial_coefficient_condition :
    ∀ (z : ℂ) (A B C D : ℂ) (r1 r2 r3 r4 r5 r6 : ℤ),
    r1 > 0 → r2 > 0 → r3 > 0 → r4 > 0 → r5 > 0 → r6 > 0 →
    (∀ (z : ℂ), z ^ 6 - 10 * z ^ 5 + A * z ^ 4 + B * z ^ 3 + C * z ^ 2 + D * z + 16 =
     (z - (r1 : ℂ)) * (z - (r2 : ℂ)) * (z - (r3 : ℂ)) * (z - (r4 : ℂ)) * (z - (r5 : ℂ)) * (z - (r6 : ℂ))) →
    B = -88 := sorry

theorem solve_equation (a b : ℝ) (h1 : a ^ 2 * b ^ 3 = 32/27) (h2 : b ^ 3 ≠ 0) (h3 : a / b ^ 3 = 27/4) : a + b = 8/3 := sorry

theorem sequence_problem (x : ℝ) (n : ℤ) (hn : n > 0) (a : ℕ → ℝ) (h1 : a 1 = 2 * x - 3) (h2 : a 2 = 5 * x - 11) (h3 : a 3 = 3 * x + 1) (d : ℝ) (hrec : ∀ k, a (k + 1) = a k + d) (hfinal : a (Int.toNat n) = 2009) : n = 502 := sorry
