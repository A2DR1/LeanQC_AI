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

theorem max_value_expr (A M C : ℕ) (h : A + M + C = 12) : (A * M * C) + (A * M) + (M * C) + (A * C) ≤ 112 := sorry

theorem not_n_gt_84 (n : ℕ) (hS : (1/2 : ℚ) + (1/3) + (1/7) + (1/n) ∈ ℤ) : ¬(n > 84) := sorry

theorem max_distance_A_B : 
  ∃ a ∈ A, ∃ b ∈ B, ∀ a' ∈ A, ∀ b' ∈ B, Complex.dist a' b' ≤ Complex.dist a b ∧ Complex.dist a b = 2 * Real.sqrt 21 := sorry

theorem f_divisibility (f : ℝ → ℝ) (h : ∀ x, f x = 4^x + 6^x + 9^x) (m n : ℕ) (hmn : m ≤ n) : ↑(f (2^m)) ∣ ↑(f (2^n)) := sorry

theorem abc_eq_neg_56 (a b c : ℝ) (h1 : 3 * a + b + c = -3) (h2 : a + 3 * b + c = 9) (h3 : a + b + 3 * c = 19) : a * b * c = -56 := sorry

theorem solve_for_x (x : ℝ) (y : ℝ) (h₁ : x + y = 25) (h₂ : x - y = 11) : x = 18 := sorry

theorem distance_between_intersection_points (f : ℝ → ℝ) (hf : ∀ x, f x = x^2) (g : ℝ → ℝ) (hg : ∀ x, g x = 1 - x) (S : Set (ℝ × ℝ)) (hS : ∀ p, p ∈ S ↔ p.2 = f p.1 ∧ p.2 = g p.1) (x1 y1 x2 y2 : ℝ) (h1 : (x1, y1) ∈ S) (h2 : (x2, y2) ∈ S) (h_ne : (x1, y1) ≠ (x2, y2)) : dist (x1, y1) (x2, y2) = Real.sqrt 10 := sorry

theorem number_of_zeros (θ : ℝ) (hθ : θ ∈ Set.Ioc 0 (2 * Real.pi)) (f : ℝ → ℝ) (hf : ∀ θ, f θ = 1 - 3 * Real.sin θ + 5 * Real.cos (3 * θ)) : Nat.card {θ ∈ Set.Ioc 0 (2 * Real.pi) | f θ = 0} = 6 := sorry

theorem charge_property (N x : ℕ) (charge : ℕ → ℕ := fun h => N + x * h) (h1 : charge 1 = 97) (h5 : charge 5 = 265) : charge 2 = 139 := sorry

theorem product_of_sqrt_terms (x : ℝ) (hx : x > 0) : 
  Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := sorry

theorem sum_digits_N_eq_9 (h : ∃! N : ℕ, ∀ n : ℕ, n ≠ N → f N > f n) : Nat.sumDigits 10 (Classical.choose h) = 9 := sorry

theorem f_lt_g (x : ℝ) (f : ℝ → ℝ := fun x => (4 * x^2) / (1 - Real.sqrt (2 * x + 1))^2) (g : ℝ → ℝ := fun x => 2 * x + 9) (h₁ : 2 * x + 1 ≥ 0) (h₂ : 1 - Real.sqrt (2 * x + 1) ≠ 0) : f x < g x := sorry

theorem sum_mod_nine (n : ℤ) (h : ∃ k, n = 3 * k) : (n + 4) + (n + 6) + (n + 8) ≡ 0 [ZMOD 9] := sorry

theorem mod_goal : 1529 ≡ 5 [MOD 6] := sorry

theorem solve_b (a b : ℕ) (ha : a = 120) (hgcd : Nat.gcd a b = 8) (hlcm : Nat.lcm a b = 3720) : b = 248 := sorry

theorem sum_of_solutions (x y z : ℤ) (equation1 : 3 * x + y = 17) (equation2 : 5 * y + z = 14) (equation3 : 3 * x + 5 * z = 41) : x + y + z = 12 := sorry

theorem binomial_sum_mod_5_ne_zero (n : ℕ) : 
  let S := Finset.Icc 0 n;
  let a := fun k ↦ Nat.choose (2 * n + 1) (2 * k + 1) * (2^3)^k;
  let X := Finset.sum S a;
  X % 5 ≠ 0 := sorry

theorem mod_congruence (n : ℤ) (h : 2 * n ≡ 15 [ZMOD 47]) : n ≡ 31 [ZMOD 47] := sorry

theorem sum_inverse_product_mod_p (p : ℕ) (hp : Nat.Prime p) (hge : p ≥ 7) : 
(∑ k in Finset.Icc 1 (p - 2), (Nat.modInv k p * Nat.modInv (k + 1) p) % p) ≡ 2 [MOD p] := sorry

theorem inequality_for_ab (a : ℝ) (b : ℝ) (h : a^2 + b^2 = 1) : a * b + (a - b) ≤ 1 := sorry

theorem product_abc (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h1 : a * (b + c) = 152) (h2 : b * (c + a) = 162) (h3 : c * (a + b) = 170) : a * b * c = 720 := sorry

theorem gcd_condition (n : ℕ) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := sorry

theorem number_of_possible_values (x : ℤ) (h : |↑x| < 3 * Real.pi) : Fintype.card {y : ℤ | |↑y| < 3 * Real.pi} = 19 := sorry

theorem recurrence_solution (y : ℤ) (a : ℕ → ℤ) (h1 : a 1 = y + 6) (h2 : a 2 = 12) (h3 : a 3 = y) (hrec : ∀ n : ℕ, a (n + 1) - a n = a (n + 2) - a (n + 1)) : y = 9 := sorry

theorem log_identity_implies_n_eq_65536 (n : ℕ) (hn : n > 0) (a : ℝ := Real.logb 4 (Real.logb 4 ↑n)) (b : ℝ := Real.logb 2 (Real.logb 16 ↑n)) (h : b = a) : n = 65536 ∧ Nat.sumOfDigits 10 n = 13 := sorry

theorem area_change (original_length original_width : ℕ) (h₁ : original_length = 3491) (h₂ : original_width = 3491) : 
  let new_length := original_length - 60;
  let new_width := original_width + 60;
  let original_area := original_length * original_width;
  let new_area := new_length * new_width;
  new_area - original_area = 3600 := sorry

theorem sum_sin_eq_tan_condition (k : ℕ) (S : Finset ℕ := Finset.Icc 1 35) (f : ℕ → ℝ := fun k => Real.sin (↑(5 * k) * (π / 180))) : ∃ (m n : ℕ), (∑ k in S, f k) = Real.tan (↑m / ↑n * (π / 180)) ∧ Nat.gcd m n = 1 ∧ ↑m / ↑n < 90 ∧ m + n = 177 := sorry

theorem solve_equations (f z : ℝ) (h1 : f + 3 * z = 11) (h2 : 3 * (f - 1) - 5 * z = -68) : f = -10 ∧ z = 7 := sorry

theorem pow_five_thirty_mod_seven : (5 : ℤ) ^ 30 ≡ 1 [ZMOD 7] := sorry

theorem smallest_positive_solution (x : ℝ) (y : ℝ) (hy : y = x^2 - 10 * x) (f : ℝ → ℝ) (hf : ∀ y, f y = 1 / (y - 29) + 1 / (y - 45) - 2 / (y - 69)) : (∃ x₀, x₀ > 0 ∧ f y = 0 ∧ ∀ x', x' > 0 → f (x'^2 - 10 * x') = 0 → x₀ ≤ x') → x = 13 := sorry

theorem star_example : star (3, 11) = 1 / 33 := sorry

theorem sum_goal (x : Fin 7 → ℝ) (h1 : ∑ k : Fin 7, (↑k + 1)^2 * x k = 1) (h2 : ∑ k : Fin 7, (↑k + 2)^2 * x k = 12) (h3 : ∑ k : Fin 7, (↑k + 3)^2 * x k = 123) : ∑ k : Fin 7, (↑k + 4)^2 * x k = 334 := sorry

theorem goal (x : ℝ) (sec tan csc cot : ℝ → ℝ) (hsec : ∀ x, sec x = 1 / Real.cos x) (htan : ∀ x, tan x = Real.sin x / Real.cos x) (hcsc : ∀ x, csc x = 1 / Real.sin x) (hcot : ∀ x, cot x = Real.cos x / Real.sin x) (h1 : sec x + tan x = 22 / 7) (m : ℤ) (n : ℕ) (hgcd : Int.gcd m ↑n = 1) (h2 : csc x + cot x = ↑m / ↑n) : ↑m + ↑n = 44 := sorry

theorem binomial_expansion : (90 + 1)^2 = 90^2 + 2 * 90 * 1 + 1^2 := sorry

theorem log_27_base_3_eq_3 : Real.log 27 / Real.log 3 = 3 := sorry

theorem abs_condition_implies_range (x : ℝ) (h : |x - 1| + |x| + |x + 1| = x + 2) : 0 ≤ x ∧ x ≤ 1 := sorry

theorem goal (a b c d : ℕ) (P : a * b * c * d = 40320) (E1 : a * b + a + b = 524) (E2 : b * c + b + c = 146) (E3 : c * d + c + d = 104) : a - d = 10 := sorry

theorem sum_condition (t : ℝ) (A : ℝ := (1 + Real.sin t) * (1 + Real.cos t)) (hA : A = 5 / 4) 
  (B : ℝ := (1 - Real.sin t) * (1 - Real.cos t)) (k m n : ℕ) (hk : k > 0) (hm : m > 0) (hn : n > 0) 
  (hgcd : Nat.gcd m n = 1) (hB : B = ↑m / ↑n - Real.sqrt ↑k) : k + m + n = 27 := sorry

theorem sum_of_special_reals (a : ℝ) (b : ℝ) (ha : a > 0) (hb : b > 0) (hne : a ≠ b) (ha_eq : a - (1 / a) = 1) (hb_eq : b - (1 / b) = 1) : a + b = Real.sqrt 5 := sorry

theorem f_value_at_3 (a b : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = a * x^4 - b * x^2 + x + 5) (hneg3 : f (-3) = 2) : f 3 = 8 := sorry

theorem inverse_function_property (f : ℝ → ℝ) (hf : Function.Bijective f) (f_inv : ℝ → ℝ) (h_inv : Function.RightInverse f_inv f ∧ Function.LeftInverse f_inv f) (h1 : f 2 = 4) (h2 : f_inv 2 = 4) : f (f 2) = 2 := sorry

theorem geometric_sequences_goal (a b : ℝ+) (seq1 : ℕ → ℝ+) (seq2 : ℕ → ℝ+) (r s : ℝ+) 
  (hseq1_1 : seq1 1 = 6) (hseq1_2 : seq1 2 = a) (hseq1_3 : seq1 3 = b) 
  (hseq1_rec : ∀ n : ℕ, seq1 (n + 1) = seq1 n * r) 
  (hseq2_1 : seq2 1 = 1 / b) (hseq2_2 : seq2 2 = a) (hseq2_3 : seq2 3 = 54) 
  (hseq2_rec : ∀ n : ℕ, seq2 (n + 1) = seq2 n * s) : 
  a = 3 * Real.sqrt 2 := sorry

theorem inverse_function_property (f h : ℝ → ℝ) (hinv : Function.RightInverse h f) (h2 : h 2 = 10) (h10 : h 10 = 1) (h1 : h 1 = 2) : f (f 10) = 1 := sorry

theorem sum_mod_condition : (∑ k in {k : ℕ | 0 < k ∧ k < 50 ∧ k % 3 = 0}, k % 10) = 78 := sorry

theorem min_value_of_f (p : ℝ) (hp : 0 < p ∧ p < 15) (f : ℝ → ℝ) (hf : ∀ x, f x = |x - p| + |x - 15| + |x - p - 15|) : ∀ x ∈ Set.Icc p 15, ∃ x₀ ∈ Set.Icc p 15, ∀ x ∈ Set.Icc p 15, f x₀ ≤ f x ∧ f x₀ = 15 := sorry

theorem mod_problem : ∃ n : ℤ, 123456 ≡ n [ZMOD 101] ∧ 0 ≤ n ∧ n < 101 ∧ n = 34 := sorry

theorem congruence_solution (x : ℤ) (h : 24 * x ≡ 15 [ZMOD 1199]) : x = -449 := sorry

theorem amc_sum (A M C : Fin 10) (AMC10 : ℕ := 10000 * ↑A + 1000 * ↑M + 100 * ↑C + 10) (AMC12 : ℕ := 10000 * ↑A + 1000 * ↑M + 100 * ↑C + 12) (h : AMC10 + AMC12 = 123422) : ↑A + ↑M + ↑C = 14 := sorry

theorem term_expansion (x : ℝ) (term1 := (x + 1)^2) (term2 := x) : term1 * term2 = x^3 + 2 * x^2 + x := sorry

theorem exists_periodic_solution (a : ℝ) (ha : a > 0) (f : ℝ → ℝ) (hf : ∀ x : ℝ, f (x + a) = 1 / 2 + Real.sqrt (f x - f x ^ 2)) : ∃ b : ℝ, b > 0 ∧ ∀ x : ℝ, f (x + b) = f x := sorry

theorem daily_calories_calculation (c : ℝ) (calories_in_tin : ℝ := 40) (percentage_of_daily : ℝ := 2 / 100) (h : calories_in_tin = percentage_of_daily * c) : c = 2000 := sorry

theorem arithmetic_sequence_problem (a : ℕ → ℤ) (d : ℤ) (h_rec : ∀ n : ℕ, a (n + 1) = a n + d) (h7 : a 7 = 30) (h11 : a 11 = 60) : a 21 = 135 := sorry

theorem smallest_n_with_gcd_condition : 
  Nat.find (fun n => Nat.gcd (↑(n^2 - n + 41)) (↑((n + 1)^2 - (n + 1) + 41)) > 1) = 41 := sorry

theorem goal (f g : ℝ → ℝ) (h_f : ∀ x, f x = x^4) (h_g : ∀ x, g x = 5 * x^2 - 6) (S : Set ℝ) (h_S : S = {x | f x = g x}) (h_card : Nat.card S = 4) (m n : ℝ) (h_mn : m > n) (h_S_eq : S = {Real.sqrt m, -Real.sqrt m, Real.sqrt n, -Real.sqrt n}) : m - n = 1 := sorry

theorem goal_B_value (P : ℂ → ℂ) (A B C D : ℂ) (r1 r2 r3 r4 r5 r6 : ℕ) (hP : ∀ z, P z = z^6 - 10 * z^5 + A * z^4 + B * z^3 + C * z^2 + D * z + 16) (hroots : ∀ z, P z = 0 ↔ z ∈ ({r1, r2, r3, r4, r5, r6} : Set ℂ)) (hsum : ∑ k in ({r1, r2, r3, r4, r5, r6} : Finset ℂ), k = 10) (hprod : ∏ k in ({r1, r2, r3, r4, r5, r6} : Finset ℂ), k = 16) : B = -88 := sorry

theorem not_prime_of_condition (K L M N : ℕ) (h₁ : K > L) (h₂ : L > M) (h₃ : M > N) (h₄ : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) : ¬ Nat.Prime (K * L + M * N) := sorry

theorem sqrt_equation_implies_a_eq_8 (a : ℝ) (h : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) : a = 8 := sorry

theorem goal (a : ℝ) (ha : a = 8) : (16 * (a^(1/3))^2)^(1/3) = 4 := sorry

theorem exists_intersection_point : ∃ (s t : ℝ), t = (fun t => 9 - 2 * t) s ∧ t = (fun s => 3 * s + 1) s ∧ (s, t) = (1, 4) := sorry

theorem sum_cubes_eq_square_sum (n : ℕ) : 
(∑ k in Finset.range n, (k : ℝ)^3) = (∑ k in Finset.range n, (k : ℝ))^2 := sorry

theorem power_relation (b : ℝ) (hb : b = 11^(1/4)) (x : ℝ) (h : b^(3 * x - 3) = 1 / 5) : b^(6 * x + 2) = 121 / 25 := sorry

theorem sum_of_solutions (x : ℝ) (equation : (x + 3)^2 = 121) : ∃ (x1 x2 : ℝ), x1 + x2 = -6 ∧ (x1 + 3)^2 = 121 ∧ (x2 + 3)^2 = 121 := sorry

theorem exposed_area_property : exposed_area 7 = 658 := sorry

theorem product_bound (n : ℕ) : ∏ k in Finset.Icc 1 n, (1 + 1 / (k : ℝ)^3) ≤ 3 - 1 / (n : ℝ) := sorry

theorem n_eq_70 (n : ℕ) (h₁ : Nat.gcd n 40 = 10) (h₂ : Nat.lcm n 40 = 280) : n = 70 := sorry

theorem total_mod_7_eq_3 : (∑ k in Finset.range 101, 2^k) % 7 = 3 := sorry

theorem solve_for_c (f : ℝ → ℝ) (h : ∀ x, f x = c * x^3 - 9 * x + 3) (h2 : f 2 = 9) : c = 3 := sorry

theorem f_eq_id (f : ℕ → ℕ) (h : ∀ n, f (n + 1) > f (f n)) : ∀ n, f n = n := sorry

theorem f_goal (f : ℚ → ℚ) (h_mul : ∀ a b ∈ ℚ, f (a * b) = f a + f b) (h_prime : ∀ p : ℕ, Nat.Prime p → f ↑p = ↑p) : f (25 / 11) < 0 := sorry

theorem sum_of_last_three_digits : 
  let n := 5^100;
  let digits := Nat.digits 10 n;
  let d0 := digits.get! 0;
  let d1 := digits.get! 1;
  let d2 := digits.get! 2;
  d2 + d1 + d0 = 13 := sorry

theorem problem (x : Fin 10) (n : ℕ) (hn : n = 2007 + 10 * ↑x) : n % 11 = 0 ∧ ↑x = 5 := sorry

theorem sqrt_minus_cbrt_eq_900 : Real.sqrt (1000000 : ℝ) - Real.cbrt (1000000 : ℝ) = 900 := sorry

theorem equation_solution (x : ℝ) (LHS : ℝ := 2 + (1 / (1 + (1 / (2 + (2 / (3 + x))))))) (RHS : ℝ := 144 / 53) : LHS = RHS → x = 3 / 4 := sorry

theorem number_of_solutions_in_interval : 
  let f : ℝ → ℝ := fun x => Real.sin ((π / 2) * Real.cos x) - Real.cos ((π / 2) * Real.sin x); 
  let I : Set ℝ := Set.Icc 0 π; 
  Fintype.card (↥{x ∈ I | f x = 0}) = 2 := sorry

theorem exists_unique_x1 : ∃! x₁ : ℝ, ∀ n : ℕ, let x : ℕ → ℝ := fun k => match k with | 1 => x₁ | (k+1) => x k * (x k + (1 / ↑k)) end in 0 < x n ∧ x n < x (n + 1) ∧ x (n + 1) < 1 := sorry

theorem f_composition (f : ℝ ∖ {-2} → ℝ) (h : ∀ (x : ℝ ∖ {-2}), f x = 1 / (↑x + 2)) : f (f (⟨1, by simp⟩ : ℝ ∖ {-2})) = 3 / 7 := sorry

theorem f_is_perfect_square (n : ℤ) (hn : n ≥ 9) : ∃ k : ℤ, ((↑(n + 2 + 1) * (n + 2).factorial - ↑(n + 1 + 1) * (n + 1).factorial) / ↑n.factorial : ℚ) = k * k := sorry

theorem log_property (x y z w : ℝ) (hx : x > 1) (hy : y > 1) (hz : z > 1) (hw : w > 0) (h1 : Real.logb x w = 24) (h2 : Real.logb y w = 40) (h3 : Real.logb (x * y * z) w = 12) : Real.logb z w = 60 := sorry

theorem polynomial_identity (A B : ℤ) (f : ℝ → ℝ) (hf : ∀ x, f x = 10 * x^2 - x - 24) (h : ∀ x, f x = (A * x - 8) * (B * x + 3)) : A * B + B = 12 := sorry

theorem goal_equation (f : ℤ → ℤ) (h_odd : ∀ n : ℤ, n % 2 = 1 → f n = n^2) (h_even : ∀ n : ℤ, n % 2 = 0 → f n = n^2 - 4 * n - 1) : 
let n0 := (4 : ℤ); 
let n1 := f n0; 
let n2 := f n1; 
let n3 := f n2; 
let n4 := f n3; 
let n5 := f n4; 
n5 = 1 := sorry

theorem f_property (f : ℝ → ℝ) (h : ∀ x : ℝ, f x + f (x - 1) = x^2) (x1 : ℝ) (hx1 : x1 = 19) (hf : f x1 = 94) : (Int.mod (Int.floor (f 94)) 1000) = 561 := sorry

theorem sum_a_1_to_4 : (a 1) + (a 2) + (a 3) + (a 4) = 3702 := sorry

theorem s_eq_6 (f s : ℕ) (h : f = 5 * s) (hprev : ↑(f - 3) + ↑(s - 3) = (30 : ℝ)) : ↑s = (6 : ℝ) := sorry

theorem real_inequality (a : ℝ) : a * (2 - a) ≤ 1 := sorry

theorem nat_power_eq_condition (x y : ℕ) (hx : x > 0) (hy : y > 0) (h : x ^ (y ^ 2) = y ^ x) : (x = 1 ∧ y = 1) ∨ (x = 16 ∧ y = 2) ∨ (x = 27 ∧ y = 3) := sorry

theorem expression_eq_10 (x : ℝ) (hx : x ≠ 0) : (12 / (x * x)) * (x^4 / (14 * x)) * (35 / (3 * x)) = 10 := sorry

theorem mod_sum_squares (a : ℤ) (ha : a ≡ 1 [ZMOD 2]) (b : ℕ) (hb : b ≡ 0 [MOD 4]) : a^2 + (↑b)^2 ≡ 1 [ZMOD 8] := sorry

theorem complex_example (i : ℂ) (hi : i^2 = -1) : (i / (2 : ℝ))^2 = (-1 : ℝ) / (4 : ℝ) := sorry

theorem sum_inequality (k : ℕ) (S : Set ℕ := {k | 2 ≤ k ∧ k ≤ 10000}) (f : ℕ → ℝ := fun k => 1 / Real.sqrt ↑k) : ∑ k in Finset.Icc 2 10000, f k < 198 := sorry

theorem numerator_over_denominator_eq_five_thirds : (2^2014 + 2^2012) / (2^2014 - 2^2012) = (5 : ℚ) / 3 := sorry

theorem prime_sum_equation (m n : ℕ) (hm : Nat.Prime m) (hn : Nat.Prime n) (k t : ℕ) (hkt : k > t) (hroot1 : k * k - m * k + n = 0) (hroot2 : t * t - m * t + n = 0) : m ^ n + n ^ m + k ^ t + t ^ k = 20 := sorry

theorem goal (p q : ℕ) (h_gcd : Nat.gcd p q = 1) (a : ℝ) (h_a : a = ↑p / ↑q) (S : Set ℝ) (h_S : ∀ x ∈ S, Int.floor x * fractional x = a * x ^ 2) (h_sum : ∑ x in S.toFinset, x = 420) : p + q = 929 := sorry

theorem term_product_eq (x : ℝ) (term1 := x + 3) (term2 := 2 * x - 6) : term1 * term2 = 2 * x^2 - 18 := sorry

theorem k_eq_18 (n : ℕ) (m : ℕ) (h_m : m = 2 * n) (k : ℕ) (h_k : k = m + 2) (h_eq : m * k = 288) : k = 18 := sorry

theorem consecutive_even_numbers_product_div (n : ℕ) (a := 2 * n) (b := 2 * n + 2) (c := 2 * n + 4) (h : a^2 + b^2 + c^2 = 12296) : (a * b * c) / 8 = 32736 := sorry

theorem exists_infinitely_many_m_with_n_satisfying_inequality : ∀ k : ℕ, ∃ m ≥ k, ∃ n : ℕ, m * n ≤ m + n := sorry

theorem circle_radius_eq_5 (x y : ℝ) (E : x^2 + 8*x + y^2 - 6*y = 0) : ∃ (a b : ℝ), (x - a)^2 + (y - b)^2 = 5^2 := sorry

theorem number_of_solutions (x : ℝ) (hx : x ∈ Set.Icc 0 (2 * Real.pi)) (f : ℝ → ℝ) (hf : ∀ x, f x = Real.tan (2 * x) - Real.cos (x / 2)) : Fintype.card {x : ℝ | x ∈ Set.Icc 0 (2 * Real.pi) ∧ f x = 0} = 5 := sorry

theorem log_identity : (Real.logb 2 80 / Real.logb 40 2) - (Real.logb 2 160 / Real.logb 20 2) = 2 := sorry

theorem inverse_mod_100 (x : ℤ) (hx : x ≡ 9⁻¹ [ZMOD 100]) : x ≡ 89 [ZMOD 100] := sorry

