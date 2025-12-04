
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


theorem exists_power_of_two_sum (a b c d : ℤ) (ha_odd : Odd a) (hb_odd : Odd b) (hc_odd : Odd c) (hd_odd : Odd d) (ha_pos : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d) (h_eq : a * d = b * c) (h_sum_ad : ∃ k : ℤ, a + d = 2 ^ k) (h_sum_bc : ∃ m : ℤ, b + c = 2 ^ m) : a = 1 := sorry

theorem inequality_of_absolute_sums (a b : ℝ) : |a + b| / (1 + |a + b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := sorry

theorem exists_n_eq_1058 : ∃ n : ℤ, 0 ≤ n ∧ n < (1399 : ℤ) ∧ (∃ k : ℤ, (160 : ℤ) * n = (1399 : ℤ) * k + 1) ∧ n = (1058 : ℤ) := sorry

theorem exists_nonprime_d : ∃ (K L M N : ℕ) (hK : K > 0) (hL : L > 0) (hM : M > 0) (hN : N > 0) (hKL : K > L) (hLM : L > M) (hMN : M > N) (h_eq : K * M + L * N = (K + L - M + N) * ((-K : ℤ) + L + M + N)), 
    ∃ (d : ℤ) (hd : d > 1), (∃ (e : ℤ), d = e * (d / e)) ∧ ¬ Nat.Prime (Int.natAbs d) := sorry

theorem inequality_sum_reciprocals (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := sorry

theorem mod_problem : ∀ (n : ℤ), (2 * n) ≡ 15 [ZMOD 47] → n ≡ 31 [ZMOD 47] := sorry

theorem exists_k_implies_b_eq_116 : 
    let m : ℤ := 121
    let a : ℤ := 24
    in ∀ (b : ℤ), 0 ≤ b → b < m → (∃ (k : ℤ), a * b - 1 = m * k) → b = 116 := sorry

theorem equation_system_solution : ∀ (x y z : ℝ), (3 * x + y = (17 : ℝ)) → (5 * y + z = (14 : ℝ)) → (3 * x + 5 * z = (41 : ℝ)) → (x + y + z = (12 : ℝ)) := sorry

theorem problem_statement : let f : ℤ → ℤ := fun n => if n % 2 = 0 then n ^ 2 - 4 * n - 1 else n ^ 2 in
    let n0 : ℤ := 4 in
    f (f (f (f (f n0)))) = 1 := sorry

theorem perfect_square_factorial_expression (n : ℤ) (hn : n ≥ 9) : ∃ (k : ℤ), ((n + 2)! - (n + 1)!) / n! = k ^ 2 := sorry

theorem exists_irrational_power_irrational_rational : ∃ (a : ℝ) (b : ℝ), Irrational a ∧ Irrational b ∧ Rational (a ^ b) := sorry

theorem gcd_conditions_imply_k_eq_five (hk : 0 < k) (hn : 0 < n) : 
    (∀ n : ℕ, 0 < n → Nat.gcd (6 * n + k) (6 * n + 3) = 1) → 
    (∀ n : ℕ, 0 < n → Nat.gcd (6 * n + k) (6 * n + 2) = 1) → 
    (∀ n : ℕ, 0 < n → Nat.gcd (6 * n + k) (6 * n + 1) = 1) → 
    k = 5 := sorry

theorem size_of_four_digit_even_digit_numbers_divisible_by_five : 
    Finset.card (Finset.filter (λ n : ℕ => (1000 ≤ n ∧ n ≤ 9999) ∧ (∀ d : ℕ, d ∈ Nat.digits 10 n → d ∈ ({0, 2, 4, 6, 8} : Finset ℕ)) ∧ 5 ∣ n) (Finset.Icc 1000 9999)) = 100 := sorry

theorem log_sum_product_eq_21000 : 
    let n1 : ℕ := 20
        n2 : ℕ := 100
        a : ℕ → ℝ := λ k => Real.log ((3 : ℝ) ^ (k ^ 2)) / Real.log ((5 : ℝ) ^ k)
        b : ℕ → ℝ := λ k => Real.log ((25 : ℝ) ^ k) / Real.log ((9 : ℝ) ^ k)
        S1 := ∑ k in Finset.Icc 1 n1, a k
        S2 := ∑ k in Finset.Icc 1 n2, b k
    in S1 * S2 = (21000 : ℝ) := sorry

theorem sum_sqrt_reciprocal_bound : 
    let n := (10000 : ℕ) in
    let S := ∑ k in Finset.Icc 2 n, (1 : ℝ) / Real.sqrt (k : ℝ) in
    S < 198 := sorry

theorem exists_n_gcd_gt_one : ∃ (n : ℕ) (hn : n > 0), Nat.gcd ((n : ℤ)^2 - (n : ℤ) + 41) (((n + 1 : ℕ) : ℤ)^2 - ((n + 1 : ℕ) : ℤ) + 41) > 1 := sorry

theorem integer_product_sum_condition (A B : ℤ) (h : ∀ (x : ℝ), 10 * x ^ 2 - x - 24 = ((A : ℝ) * x - 8) * ((B : ℝ) * x + 3)) : A * B + B = 12 := sorry

theorem inequality_positive_reals (a b : ℝ) (ha_pos : a > 0) (hb_pos : b > 0) (hle : b ≤ a) : ((a + b) / 2) - Real.sqrt (a * b) ≤ ((a - b)^2) / (8 * b) := sorry

theorem size_of_T_is_672 : Finset.card (Finset.filter (λ d : ℕ => ∃ k : ℤ, (d : ℤ) = k ^ 2) (Finset.filter (λ d : ℕ => d ∣ ∏ i in Finset.Icc 1 9, (Nat.factorial i)) Finset.univ)) = 672 := sorry

theorem infinite_set_size : ∀ k : ℕ, ∃ m : ℕ, m > 0 ∧ (∃ n : ℕ, n > 0 ∧ m * n ≤ m + n) ∧ k ≤ m := sorry

theorem complex_identity : 
    let V : ℂ := 1 + Complex.I
    let Z : ℂ := 2 - Complex.I
    let I : ℂ := ?_ in
    (V = I * Z) → (I = (1/5 : ℂ) + (3/5 : ℂ) * Complex.I) := sorry

theorem exists_n_not_gt_84 (hpos : 0 < n) (hS_int : (1/2 : ℚ) + (1/3 : ℚ) + (1/7 : ℚ) + (1 / (n : ℚ)) ∈ ℤ) : ∃ n, ¬(n > 84) := sorry

theorem exists_int_r : ∃ (r : ℤ), ∃ (q : ℤ), (5 : ℤ) ^ (30 : ℕ) = (7 : ℤ) * q + r ∧ r = (1 : ℤ) := sorry

theorem problem_statement : ∀ (n : ℕ) (k1 k2 : ℤ), a = 10 * k1 → n = 10 * k2 → Int.gcd k1 k2 = 1 → n * a = 10 * b → n = 70 := sorry

theorem product_identity : 
    let T : ℕ → ℕ := λ k => (2 ^ (2 ^ k)) + (3 ^ (2 ^ k)) in
    let P := ∏ k in Finset.Icc 0 6, T k in
    P = (3 ^ 128) - (2 ^ 128) := sorry

theorem problem (a b c : ℝ) (h : ∀ x : ℝ, (fun (x : ℝ) => x^3 + a * x^2 + b * x + c) x = ((x - Real.cos ((2 : ℝ) * π / 7)) * (x - Real.cos ((4 : ℝ) * π / 7)) * (x - Real.cos ((6 : ℝ) * π / 7)))) : a * b * c = 1/32 := sorry

theorem sum_of_even_terms : 
    let n : ℕ := 98
    let d : ℝ := 1
    (a : ℕ → ℝ) (h_arith : ∀ k, a (k + 1) = a k + d) (h_sum : ∑ k in Finset.range n, a (k + 1) = 137) in
    ∑ k in Finset.filter (λ k => k % 2 = 0) (Finset.range n), a (k + 2) = 93 := sorry

theorem intersection_point_sum_eq_four : ∃ (x_A y_A : ℝ), y_A = (1/3 : ℝ) * x_A ∧ y_A = (11 - 2 * x_A) / 5 ∧ x_A + y_A = 4 := sorry

theorem exists_int_divisible_by_prime (hp : Nat.Prime p) (ha : a > 0) : ∃ (k : ℤ), (a : ℤ) ^ p - a = p * k := sorry

theorem size_of_set_with_negative_f : Finset.card ((Finset.mk {x | x ∈ ({17/32 : ℚ}, 11/16, 7/9, 7/6, 25/11)}).filter (λ x : ℚ => f x < 0)) = 1 := sorry

theorem problem : ∀ (a : ℝ) (f : ℝ → ℝ), (∀ x, f x = Real.sqrt (4 + Real.sqrt (16 + (16 * x))) + Real.sqrt (1 + Real.sqrt (1 + x))) → (f a = 6) → (a = 8) := sorry

theorem inequality_under_circle_constraint (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : a * b + (a - b) ≤ 1 := sorry

theorem floor_sum_equation : 
    let N : ℝ := 1/3 in
    let f : ℝ → ℤ := λ x => ⌊x⌋ in
    f (10 * N) + f (100 * N) + f (1000 * N) + f (10000 * N) = 3702 := sorry

theorem inequality_sum_of_squares_over_previous (a b c d : ℝ) (ha_pos : 0 < a) (hb_pos : 0 < b) (hc_pos : 0 < c) (hd_pos : 0 < d) :
    (a ^ 2 / b) + (b ^ 2 / c) + (c ^ 2 / d) + (d ^ 2 / a) ≥ a + b + c + d := sorry

theorem units_digit_product : 
    let a := (16 : ℕ) 
    b := (17 : ℕ) 
    c := (18 : ℕ) 
    x := (17 : ℕ) 
    y := (18 : ℕ) 
    z := (19 : ℕ) 
    f := (λ n : ℕ => a ^ n) 
    g := (λ n : ℕ => b ^ n) 
    h := (λ n : ℕ => c ^ n) 
    u := (λ m : ℕ => m % 10) in
    u (f x * g y * h z) = 8 := sorry

theorem size_of_set_where_f_equals_g : 
    let I : Set ℝ := Set.Icc (0 : ℝ) π
    let f : ℝ → ℝ := fun x : ℝ => Real.sin ((π / 2) * Real.cos x)
    let g : ℝ → ℝ := fun x : ℝ => Real.cos ((π / 2) * Real.sin x) in
    Finset.card (Finset.filter (fun x : ℝ => f x = g x) (Set.Finite.toFinset (Set.Finite.subtype (Set.Finite_Icc (0 : ℝ) π) (by exact ?_)))) = 2 := sorry

theorem max_value_of_f : sSup (Set.range (fun (t : ℝ) => ((2^t - 3*t) * t) / (4^t))) = 1/12 := sorry

theorem exists_minimum_of_quadratic : ∃ (x : ℝ), ∀ (y : ℝ), (x ^ 2 - (14 * x + 3)) ≤ (y ^ 2 - (14 * y + 3)) := sorry

theorem max_sum_of_factors_of_2001 : 
    let year := 2001 in
    ∀ (I M O : ℕ) (hI : I > 0) (hM : M > 0) (hO : O > 0) (hdistinct : I ≠ M ∧ I ≠ O ∧ M ≠ O) (hprod : I * M * O = year),
    I + M + O ≤ 671 := sorry

theorem size_of_solutions : Finset.card (Finset.filter (λ x : ℝ => Real.tan (2 * x) = Real.cos (x / 2)) (Finset.Icc (0 : ℝ) (2 * π) : Finset ℝ)) = 5 := sorry

theorem min_sum_of_m_n (m n : ℕ) (hm : m > 0) (hn : n > 0) (d : ℕ := 8) (L : ℕ := 112) (h_gcd : Nat.gcd m n = d) (h_lcm : Nat.lcm m n = L) : 
    ∃ (k : ℕ), m + n = k ∧ ∀ (x y : ℕ), x > 0 → y > 0 → Nat.gcd x y = d → Nat.lcm x y = L → k ≤ x + y := sorry

theorem sum_digits_f_100_eq_13 : 
    let n : ℕ := 100
    let f : ℕ → ℕ := λ k => (5 ^ k) % 1000
    in (Nat.digits 10 (f n)).sum = 13 := sorry

theorem parity_of_sequence : 
    let D : ℕ → ℤ := fun n => 
      match n with
      | 0 => 0
      | 1 => 0
      | 2 => 1
      | n + 3 => D (n + 2) + D n
      end
    in 
    (Even (D 2021) ∧ Odd (D 2022) ∧ Even (D 2023)) := sorry

theorem inequality_for_nth_root (n : ℕ) (hn : n > 0) : (Real.log (n : ℝ)) / (n : ℝ) ≤ Real.log (2 - (1 : ℝ) / (n : ℝ)) := sorry

theorem product_abc_eq_720 (a b c : ℝ) (ha_pos : a > 0) (hb_pos : b > 0) (hc_pos : c > 0) (h1 : a * (b + c) = 152) (h2 : b * (c + a) = 162) (h3 : c * (a + b) = 170) : a * b * c = 720 := sorry

theorem exists_int_q : ∃ q : ℤ, (1529 : ℤ) = (6 : ℤ) * q + 5 := sorry

theorem square_relation : (91 : ℕ)^2 = 8281 := sorry

theorem log_base_eq : Real.logb (3 : ℝ) (27 : ℝ) = 3 := sorry

theorem eq_neg_two (a : ℝ) (h : (8 : ℝ)⁻¹ / (4 : ℝ)⁻¹ = a) : a = -2 := sorry

theorem complex_condition_implies_sum (z : ℂ) (a b c : ℝ) (ha : a = Complex.normSq z) (hb : b = Complex.normSq (z + 2)) (hc : c = Complex.normSq (z ^ 2 + 1)) (h : 12 * a = 2 * b + c + 31) : z + 6 / z = -2 := sorry

theorem problem (x y : ℝ) (hA : ℝ := 7) (hG : ℝ := Real.sqrt 19) (h1 : (x + y) / 2 = hA) (h2 : Real.sqrt (x * y) = hG) : x ^ 2 + y ^ 2 = 158 := sorry

theorem cube_root_condition_implies_cube_plus_inverse_cube (r : ℝ) (hpos : r > 0) (h : r^(1/3 : ℝ) + (1 / r^(1/3 : ℝ)) = 3) : r^3 + (1 / r^3) = 5778 := sorry

theorem exists_unique_x1 : ∃! (x1 : ℝ), ∀ (n : ℕ) (hn : n ≥ 1), let seq : ℕ → ℝ := fun k => Nat.recOn k x1 fun m seq_m => seq_m * (seq_m + (1 : ℝ) / (m : ℝ)) in
  0 < seq n ∧ seq n < seq (n + 1) ∧ seq (n + 1) < 1 := sorry

theorem max_distance_eq_two_sqrt_twenty_one : 
    let A : Set ℂ := {z | z ^ 3 - 8 = 0}
    let B : Set ℂ := {z | z ^ 3 - 8 * z ^ 2 - 8 * z + 64 = 0}
    let dist (u v : ℂ) : ℝ := Real.sqrt (((u.re - v.re) ^ 2) + ((u.im - v.im) ^ 2))
    in sSup (Set.image2 dist A B) = 2 * Real.sqrt 21 := sorry

theorem exists_int_k (n : ℕ) : ∃ (k : ℤ), (10 : ℤ) ^ n - ((-1 : ℤ) ^ n) = 11 * k := sorry

theorem product_bound (n : ℕ) (a : ℕ → ℝ) (h_nonneg : ∀ i, 0 ≤ a i) (h_sum : ∑ i in Finset.range n, a i = n) : ∏ i in Finset.range n, a i ≤ 1 := sorry

theorem log_problem (x y : ℝ) (hx_pos : x > 0) (hy_pos : y > 0) (hx_ne_one : x ≠ 1) (hy_ne_one : y ≠ 1) (h_log_eq : Real.logb 2 x = Real.logb y 16) (h_prod_eq : x * y = 64) : (Real.logb 2 (x / y)) ^ 2 = 20 := sorry

theorem solve_for_c : 
    let f : ℝ → ℝ := λ x => c * (x ^ 3) - 9 * x + 3
    let x : ℝ := 2
    in f 2 = 9 → c = 3 := sorry

theorem inequality_lemma (x : ℝ) (n : ℕ) (hx : x > -1) : (1 + (n : ℝ) * x) ≤ ((1 + x) ^ n) := sorry

theorem mod_problem : 
    let m : ℕ := 101 in
    ∀ (n : ℤ), 0 ≤ n → n < (m : ℤ) → (123456 : ℤ) % (m : ℤ) = n → n = (34 : ℤ) := sorry

theorem father_son_age_problem : ∀ (f s : ℤ), f = 5 * s → ((f - 3) + (s - 3)) = 30 → s = 6 := sorry

theorem arithmetic_sequence_sum_properties (a d : ℝ) (hS5 : S 5 = (70 : ℝ)) (hS10 : S 10 = (210 : ℝ)) : a = 42/5 := sorry

theorem remainder_of_product_mod_four : ((121 : ℕ) * 122 * 123) % 4 = 2 := sorry

theorem sum_mod_four_eq_two : (∑ i in Finset.range 13, i) % 4 = 2 := sorry

theorem f_value_at_four : f 4 = 11 := sorry

theorem sum_of_solutions : 
    let f : ℝ → ℝ := λ x => |2 - x| in
    let S_set : Set ℝ := {x | f x = 3} in
    let x₁ x₂ : ℝ := Classical.choose (Set.exists_pair_of_ne_singleton ?_) in
    let S : ℝ := x₁ + x₂ in
    S = 4 := sorry

theorem product_of_S_eq_20 : 
    let P : ℝ → ℝ := fun x => x^2 + 18*x + 30
    let Q : ℝ → ℝ := fun x => x^2 + 18*x + 45
    let S : Set ℝ := {r | P r = 2 * Real.sqrt (Q r)} in
    (∀ x : ℝ, P x = 2 * Real.sqrt (Q x)) → (∏ r in S, r) = 20 := sorry

theorem f_of_three_eq_eight (a b : ℝ) (h : (fun (x : ℝ) => a * (x ^ 4) - b * (x ^ 2) + x + 5) (-3) = 2) : (fun (x : ℝ) => a * (x ^ 4) - b * (x ^ 2) + x + 5) (3) = 8 := sorry

theorem problem_statement : ∃ (a b c d : ℕ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a * b * c * d = 40320 ∧ a * b + a + b = 524 ∧ b * c + b + c = 146 ∧ c * d + c + d = 104 ∧ a - d = 10 := sorry

theorem base_representation : let a := 1222; base := 3 in a = 53 := sorry

theorem congruence_property (n : ℕ) (hn : n > 0) : (3^(2^n) - 1) ≡ 2^(n+2) [MOD 2^(n+3)] := sorry

theorem sequence_problem (a d : ℝ) (f : ℕ → ℝ) (h_def : ∀ n, f n = a + ((n : ℝ) - 1) * d) (h_f7 : f 7 = 30) (h_f11 : f 11 = 60) : f 21 = 135 := sorry

theorem f_84_eq_997 : f 84 = 997 := sorry

theorem f_zero_for_all_integers : ∀ (f : ℤ → ℤ), (∀ (a b : ℤ), f (2 * a) + 2 * f b = f (f (a + b))) → ∀ (x : ℤ), f x = 0 := sorry

theorem f_g_at_two : (fun (x : ℝ) => x + 1) ((fun (x : ℝ) => x ^ 2 + 3) (2 : ℝ)) = (8 : ℝ) := sorry

theorem solve_system (a b : ℝ) (h1 : 3 * a + 2 * b = 5) (h2 : a + b = 2) : (a, b) = (1, 1) := sorry

theorem size_of_E_set : Finset.card (Finset.filter (λ E => E ∈ ({22, 60, 119, 180, 231} : Finset ℕ)) (Finset.image (λ (pair : ℕ × ℕ) => pair.1 * pair.2 - (pair.1 + pair.2)) ((Finset.filter (λ (pair : ℕ × ℕ) => pair.1 ≠ pair.2) (({5, 7, 11, 13, 17} : Finset ℕ) ×ˢ ({5, 7, 11, 13, 17} : Finset ℕ))))))) = 1 := sorry

theorem remainder_eq_six : (239 + 174 + 83) % 10 = 6 := sorry

theorem f_property (f : ℕ × ℕ → ℕ) (h1 : ∀ x : ℕ, f (x, x) = x) (h2 : ∀ x y : ℕ, f (x, y) = f (y, x)) (h3 : ∀ x y : ℕ, (x + y) * f (x, y) = y * f (x, x + y)) : f (14, 52) = 364 := sorry

theorem cube_root_property : ((16 : ℝ) * ((8 : ℝ)^2)^(1/3 : ℝ))^(1/3 : ℝ) = 4 := sorry

theorem sqrt_product_identity (x : ℝ) (hx : x ≥ 0) : (Real.sqrt (60 * x)) * (Real.sqrt (12 * x)) * (Real.sqrt (63 * x)) = 36 * x * Real.sqrt (35 * x) := sorry

theorem water_consumption : w₂ = 5 := sorry

theorem set_size_eq_six : 
    let f : ℝ → ℝ := fun θ => 1 - 3 * Real.sin θ + 5 * Real.cos (3 * θ) in
    Finset.card (Finset.filter (fun θ => f θ = 0) (Finset.Ioo (0 : ℝ) (2 * π) ∪ Finset.Icc (2 * π) (2 * π))) = 6 := sorry

theorem log_sqrt_identity : 
    let a := (6 : ℝ) in
    let b := (2 : ℝ) in
    let c := (3 : ℝ) in
    let L1 := Real.logb b a in
    let L2 := Real.logb c a in
    let S := Real.sqrt (L1 + L2) in
    S = Real.sqrt (Real.logb b c) + Real.sqrt (Real.logb c b) := sorry

theorem inequality_of_power_means (a b : ℝ) (ha : a > 0) (hb : b > 0) (n : ℕ) (hn : n > 0) : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := sorry

theorem sum_power_condition (a b x y : ℝ) (h1 : a * x + b * y = 3) (h2 : a * (x ^ 2) + b * (y ^ 2) = 7) (h3 : a * (x ^ 3) + b * (y ^ 3) = 16) (h4 : a * (x ^ 4) + b * (y ^ 4) = 42) : a * (x ^ 5) + b * (y ^ 5) = 20 := sorry

theorem exists_periodic_function (a : ℝ) (ha : a > 0) (f : ℝ → ℝ) (hf : ∀ x : ℝ, f (x + a) = 1/2 + Real.sqrt (f x - (f x)^2)) : ∃ b : ℝ, b > 0 ∧ ∀ x : ℝ, f (x + b) = f x := sorry

theorem units_digit_of_sum : ((29 : ℕ) * 79 + 31 * 81) % 10 = 2 := sorry

theorem exists_int_r : ∃ r : ℤ, r = 7 ∧ (194 : ℤ) ≡ r [ZMOD (11 : ℤ)] := sorry

theorem inequality_chain (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : a + b + c = 2) (h4 : a * b + b * c + c * a = 1) : 0 ≤ a ∧ a ≤ 1/3 ∧ 1/3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4/3 := sorry

theorem size_of_set_S : Finset.card (Finset.filter (λ (x : ℤ) => |x| < 3 * π) Finset.univ) = 19 := sorry

theorem absolute_value_condition (a b : ℕ) (h_sum : a + b = 17402) (h_div : 10 ∣ a) (h_eq : b = Nat.find? (fun k : ℕ => a = 10 * k)) : |(a : ℤ) - (b : ℤ)| = 14238 := sorry

theorem problem : ∀ (a b : ℕ → ℝ) (h_init : a 100 = (2 : ℝ) ∧ b 100 = (4 : ℝ)) (h_rec : ∀ n : ℕ, n ≥ 1 → a (n + 1) = Real.sqrt 3 * a n - b n ∧ b (n + 1) = Real.sqrt 3 * b n + a n), a 1 + b 1 = 1 / ((2 : ℝ) ^ 98) := sorry

theorem prime_equation (m n : ℕ) (hm : Nat.Prime m) (hn : Nat.Prime n) (k t : ℕ) (hkpos : k > 0) (htpos : t > 0) (hkt : k > t) (h : ∀ x : ℝ, x^2 - (m : ℝ) * x + (n : ℝ) = (x - (k : ℝ)) * (x - (t : ℝ))) : m^n + n^m + k^t + t^k = 20 := sorry

theorem formalized_theorem (n : ℕ) (hpos : n > 0) (h_eq : (2 * n) * (2 * n + 2) = 288) : (2 * n + 2) = 18 := sorry

theorem sum_of_roots_eq_sqrt_five (a b : ℝ) (ha_pos : a > 0) (hb_pos : b > 0) (h_ne : a ≠ b) (ha_eq : a - (1 / a) = 1) (hb_eq : b - (1 / b) = 1) : a + b = Real.sqrt 5 := sorry

theorem inequality_condition (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h1 : a + b > c) (h2 : b + c > a) (h3 : c + a > b) : 
    (a ^ 2 * ((b + c) - a)) + (b ^ 2 * ((c + a) - b)) + (c ^ 2 * ((a + b) - c)) ≤ 3 * a * b * c := sorry

theorem polynomial_coefficient_condition (A B C D : ℤ) (r1 r2 r3 r4 r5 r6 : ℕ) (hr1 : r1 > 0) (hr2 : r2 > 0) (hr3 : r3 > 0) (hr4 : r4 > 0) (hr5 : r5 > 0) (hr6 : r6 > 0) : 
    (∀ z : ℂ, (z ^ 6 + ((-10 : ℂ) * z ^ 5) + (A : ℂ) * z ^ 4 + (B : ℂ) * z ^ 3 + (C : ℂ) * z ^ 2 + (D : ℂ) * z + 16) = 
    ((z - (r1 : ℂ)) * (z - (r2 : ℂ)) * (z - (r3 : ℂ)) * (z - (r4 : ℂ)) * (z - (r5 : ℂ)) * (z - (r6 : ℂ)))) → 
    B = -88 := sorry

theorem solve_system (a b : ℝ) (h1 : a ^ 2 * b ^ 3 = 32 / 27) (h2 : a / (b ^ 3) = 27 / 4) : a + b = 8 / 3 := sorry

theorem sequence_problem (x : ℝ) (a : ℕ → ℝ) (h_a1 : a 1 = 2 * x - 3) (h_a2 : a 2 = 5 * x - 11) (h_a3 : a 3 = 3 * x + 1) (h_real : ∀ i, a i = a i) (d : ℝ) (h_arithmetic : ∀ i, a (i + 1) = a i + d) (n : ℕ) (h_an : a n = 2009) : n = 502 := sorry

