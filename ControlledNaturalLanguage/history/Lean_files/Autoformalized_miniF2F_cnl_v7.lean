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

/-- Assumptions:
Define the set S = {1, 3, 5, 7, 9, 11, 13}.
Goal:
The ones digit of the product of all elements in S is 5. -/
theorem ones_digit_prod_S : (∏ x in ({1, 3, 5, 7, 9, 11, 13} : Finset ℕ), x).mod 10 = 5 := sorry

/-- Assumptions:
Define f : ℝ → ℝ by f(x) = x^4.
Define g : ℝ → ℝ by g(x) = (5*(x^2)) - 6.
Assume for all real numbers x, f(x) = g(x) if and only if x is in the set {a, b, c, d}.
Assume a = √(m).
Assume b = -√(m).
Assume c = √(n).
Assume d = -√(n).
Assume m > n.
Assume m is a real number.
Assume n is a real number.
Goal:
(m - n) = 1. -/
theorem m_minus_n_eq_one (f g : ℝ → ℝ) (a b c d : ℝ) (m n : ℝ) (hm : m > n) (h₁ : ∀ x, f x = x^4) (h₂ : ∀ x, g x = 5 * x^2 - 6) (h₃ : a = Real.sqrt m) (h₄ : b = -Real.sqrt m) (h₅ : c = Real.sqrt n) (h₆ : d = -Real.sqrt n) : m - n = 1  :=  by sorry

/-- Assumptions:
Define m = 121.
Define a = 24.
Let b be an integer.
Assume (a * b) ≡ 1 mod m.
Goal:
b = 116. -/
theorem b_eq_116 : b = 116 := sorry

/-- Assumptions:
Let n be a natural number.
Goal:
There exists an integer k such that ((4^(n+1)) + 20) = 12 * k. -/
theorem four_pow_add_twenty_dvd_by_twelve : ∀ n : ℕ, ∃ k : ℤ, (4:ℝ)^(n+1) + 20 = 12 * k := sorry

/-- Assumptions:
Define ℝ as the set of real numbers.
Let x be a real number.
Assume (3 - x) ≥ 0.
Assume (x + 1) ≥ 0.
Assume (√(3 - x) - √(x + 1)) ≥ 0.
Define f : ℝ → ℝ by f(x) = √(√(3 - x) - √(x + 1)).
Goal:
The set of real numbers x such that (f(x) > (1 / 2)) is equal to the interval [ -1, (1 - (√(127) / 32)) ). -/
theorem f_pos_interval : {x | 1 / 2 < f x} = Icc (-1 : ℝ) (1 - √(127) / 32) := sorry

/-- Assumptions:
Define n = 100.
Define S = 1 + 2 + 3 + ... + n.
Goal:
S mod 6 = 4. -/
theorem sum_range_nat_mod_six_eq_four : (∑ k in range 100, k) % 6 = 4 := sorry

Goal:  
The size of the set {n in ℕ | n > 0 and (n + 1000) / 70 = floor(sqrt(n))} = 6. -/
theorem card_filter_condition_eq_six : (filter (fun n => 0 < n ∧ (n + 1000) / 70 = ⌊Real.sqrt n⌋) (Icc 1 1000)).card = 6 := sorry

/-- Assumptions:
Define ℕ as the set of natural numbers.
Define ℤ as the set of integers.
Define ℝ as the set of real numbers.
Let n be a natural number.
Assume n > 1.
Assume there exists an integer k such that n = k^3.
Assume there exists an integer m such that n = m^4.
Goal:
n = 4096. -/
theorem n_eq_4096 (n : ℕ) (hn : 1 < n) (k : ℤ) (hk : ↑k ^ 3 = ↑n) (m : ℤ) (hm : ↑m ^ 4 = ↑n) : n = 4096 := sorry

Goal:
(a = 0) AND (b = 0) AND (c = 0). -/
theorem a_eq_b_eq_c_eq_zero_of_a_add_b_mul_m_add_c_mul_n_eq_zero {a b c : ℚ} {m n : ℝ}
    (hm : 0 < m) (hn : 0 < n) (h1 : m^3 = 2) (h2 : n^3 = 4) (h3 : a + b * m + c * n = 0) :
    a = 0 ∧ b = 0 ∧ c = 0  :=  by sorry

/-- Assumptions:
Define F : ℕ → ℕ.
Define F(0) = 1.
Define F(1) = 1.
For every natural number n ≥ 2, define F(n) = F(n-1) + F(n-2).
Goal:
(F(99) mod 4) = 3. -/
theorem fib_99_mod_4 : (fib 99) % 4 = 3 := sorry

/-- Assumptions:
Define n be an integer.
Assume n > 10.
There exists an integer k such that n = k^2.
There exists an integer m such that n = m^3.
Goal:
n = 64. -/
theorem {n : ℤ} (h : n > 10) (k : ℤ) (hk : n = k^2) (m : ℤ) (hm : n = m^3) : n = 64 := sorry

/-- Assumptions:
Let n be a natural number.
For every integer i in the set {1, ..., n}, define a_i : ℝ.
Assume for every integer i in the set {1, ..., n}, a_i ≥ 0.
Assume (∑_{i=1}^{n} a_i) = n.
Goal:
(∏_{i=1}^{n} a_i) ≤ 1. -/
theorem geom_mean_le_one_extracted (n : ℕ) (a : Fin n → ℝ) (ha : ∀ (i : Fin n), 0 ≤ a i) : ∑ i, a i = ↑n → ∏ i, a i ≤ 1 := sorry

/-- Assumptions:
Define N = 10000.
Define S : ℕ → ℝ by S(n) = sum for k in the set {2, ..., n} of (1 / sqrt(k)).
Goal:
S(N) < 198. -/
theorem s_lt_one_nine_eight : s 10000 < 198 := sorry

/-- Assumptions:
Define f : ℝ → ℝ by f(x) = x^2.
Define g : ℝ → ℝ by g(x) = 1 - x.
Let x be a real number.
Assume f(x) = g(x).
Goal:
The distance between the points (x1, f(x1)) and (x2, f(x2)) = √(10). -/
theorem distance_between_points_eq_sqrt_10 (x1 x2 : ℝ) (f g : ℝ → ℝ) (hf : f = fun x => x^2) (hg : g = fun x => 1 - x) (h : f x1 = g x2) : Real.sqrt 10 = dist (x1, f x1) (x2, f x2) := sorry

/-- Assumptions:
Define a = 40.
Define b = 280.
Let n be a natural number.
Assume there exists an integer k1 such that a = (gcd(n, a)) * k1.
Assume there exists an integer k2 such that n = (gcd(n, a)) * k2.
Assume gcd(k1, k2) = 1.
Assume (gcd(n, a)) * (lcm(n, a)) = n * a.
Goal:
n = 70. -/
theorem n_eq_70_extracted {a b n : ℕ} : ((a = (a.gcd n) * (b.gcd a)) ∧ (n = (a.gcd n) * (n.lcm a))) ∧ (a.gcd n).Coprime (b.gcd a) → n = 70 := sorry

/-- Assumptions:
Define f : ℝ → ℝ by f(x) = (x + 1).
Define g : ℝ → ℝ by g(x) = (x^2 + 3).
Goal:
f(g(2)) = 8. -/
theorem f_g_two : f (g 2) = 8 := sorry

/-- Assumptions:
Define a rational number a.
Define (8^(-1)) = (1 / 8).
Define (4^(-1)) = (1 / 4).
Goal:
a = -2. -/
theorem rational_a_eq_neg_two : (1 / 8 : ℚ) + (1 / 4 : ℚ) + (-2 : ℚ) = -2 := sorry

/-- Assumptions:
Let x be an integer.
Let y be an integer.
Assume (y^2) + (3 * (x^2) * (y^2)) = (30 * (x^2)) + 517.
Goal:
(3 * (x^2) * (y^2)) = 588. -/
theorem diff_of_int_ext (x y : ℤ) (h : y^2 + 3 * x^2 * y^2 = 30 * x^2 + 517) : 3 * x^2 * y^2 = 588 := sorry

/-- Assumptions:
Let n be a natural number.
Assume n > 0.
Define P : ℕ → ℚ by P(n) = ∏_{k in the set {1, ..., n}} (1 + (1 / (2^k))).
Goal:
P(n) < (5 / 2). -/
theorem prod_lt_five_div_two {n : ℕ} (hn : 0 < n) : (∏ k in Finset.Icc 1 n, (1 + (1 / (2 ^ k)))) < 5 / 2 := sorry

/-- Assumptions:
Define a = 29.
Define b = 79.
Define c = 31.
Define d = 81.
Goal:
The units digit of ((a * b) + (c * d)) is 2. -/
theorem units_digit_of_multiplication_addition (a b c d : ℕ) (ha : a = 29) (hb : b = 79) (hc : c = 31) (hd : d = 81) : (a * b + c * d) % 10 = 2 := sorry

/-- Assumptions:
Let a be a positive real number.
Let b be a positive real number.
Let c be a positive real number.
Let d be a positive real number.
Goal:
((a^2) / b) + ((b^2) / c) + ((c^2) / d) + ((d^2) / a) ≥ a + b + c + d. -/
theorem lean_4_ineq_extracted {a b c d : ℝ} : a > 0 → b > 0 → c > 0 → d > 0 → a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := sorry

/-- The maximum value of f(t) for real numbers t is 1/12. -/
theorem max_value_f_real : ∀ t : ℝ, (2^t - 3*t) * t / 4^t ≤ 1/12 := sorry

Goal:
((12 / (x * x)) * ((x^4) / (14 * x)) * (35 / (3 * x))) = 10. -/
theorem calculate_expression (x : ℝ) (hx : x ≠ 0) : (12 / (x * x)) * (x^4 / (14 * x)) * (35 / (3 * x)) = 10 := sorry

Goal:  
X = 14. -/
theorem X_eq_14 (hX : ∃ k : ℤ, X = 3 * k + 2) (hX' : ∃ m : ℤ, X % 10 = (5 * m + 4) % 10) : X = 14 := sorry

Goal:  
(a*(x^5) + b*(y^5)) = 20. -/
theorem a_x_pow_5_add_b_y_pow_5_eq_20 (a b x y : ℝ) (h₁ : a * x + b * y = 3) (h₂ : a * x ^ 2 + b * y ^ 2 = 7) (h₃ : a * x ^ 3 + b * y ^ 3 = 16) (h₄ : a * x ^ 4 + b * y ^ 4 = 42) : a * x ^ 5 + b * y ^ 5 = 20 := sorry

/-- Assumptions:
Define a = 8.
Goal:
((16 * (a^2)^(1/3)))^(1/3) = 4. -/
theorem example_with_a (a : ℝ) (ha : a = 8) : (16 * (a^2)^(1/3))^(1/3) = 4 := sorry

Goal:  
(z / x) = (7 / 25). -/
theorem div_eq_div_of_eq_mul_of_eq_mul_extracted {x y z : ℝ} : 2 * x = 5 * y → 7 * y = 10 * z → z / x = 7 / 25 := sorry

/-- Assumptions:
Define a ∈ ℝ.
Define b ∈ ℝ.
Define c ∈ ℝ.
Define d ∈ ℝ.
Assume (4^a) = 5.
Assume (5^b) = 6.
Assume (6^c) = 7.
Assume (7^d) = 8.
Goal:
(a * b * c * d) = (3/2). -/
theorem mul_mul_mul_mul_extracted {a b c d : ℝ} : 4 ^ a = 5 → 5 ^ b = 6 → 6 ^ c = 7 → 7 ^ d = 8 → a * b * c * d = 3 / 2 := sorry

/-- Assumptions:
Define A = 180.
Define P = 54.
Let L be a positive real number.
Let W be a positive real number.
Assume (L * W) = A.
Assume (2 * (L + W)) = P.
Goal:
((L)^2 + (W)^2) = 369. -/
theorem length_width_squared_sum (A : ℝ) (P : ℝ) (L W : ℝ) (hA : A = 180) (hP : P = 54) (hL : 0 < L) (hW : 0 < W) (hA' : L * W = A) (hP' : 2 * (L + W) = P) : L^2 + W^2 = 369 := sorry

Goal:  
(S1(20)) * (S2(100)) = 21000. -/
theorem final_product : (∑ k in Finset.Icc 1 20, Real.logb (5^k) (3^(k^2))) * (∑ k in Finset.Icc 1 100, Real.logb (9^k) (25^k)) = 21000 := sorry

/-- Assumptions:
Define m be a prime number.
Define n be a prime number.
Define k be a positive integer.
Define t be a positive integer.
Assume k > t.
Assume for every real number x, (x^2) - (m * x) + n = (x - k) * (x - t).
Goal:
(m^n) + (n^m) + (k^t) + (t^k) = 20. -/
theorem m_n_k_t_eq_20 (m n k t : ℕ) (hm : m.Prime) (hn : n.Prime) (hk : 0 < k) (ht : 0 < t)
    (h : ∀ x : ℝ, x^2 - m * x + n = (x - k) * (x - t)) : m^n + n^m + k^t + t^k = 20 := sorry

/-- Assumptions:
Define a = 120.
Define a as a natural number.
Define b as a natural number.
Define l = 3720.
Define d = 8.
Assume l is the least common multiple of a and b.
Assume d is the greatest common divisor of a and b.
Goal:
b = 248. -/
theorem b_eq_248 (a b l d : ℕ) (hl : l = 3720) (hA : a = 120) (hd : d = 8) (hab : a.lcm b = l) (h : a.gcd b = d) : b = 248 := sorry

/-- Assumptions:
Define n = 999999.
Goal:
The remainder when (5^n) is divided by 7 is 6. -/
theorem remainder_of_power_5_by_7 :
  (5^999999) % 7 = 6 := sorry

/-- Assumptions:
Define f : ℕ → ℕ.
Define f(2) = 0.
Assume f(3) > 0.
Define f(9999) = 3333.
Assume for all natural numbers m and n, (f(m + n) - f(m) - f(n)) = 0 or (f(m + n) - f(m) - f(n)) = 1.
Goal:
f(1982) = 660. -/
theorem f_1982 : f 1982 = 660 := sorry

/-- Assumptions:
Define y as a real number.
Assume (√(19 + (3*y))) = 7.
Goal:
y = 10. -/
theorem y_eq_10 : √(19 + 3 * y) = 7 → y = 10 := sorry

Goal:
T(5) = (11 / 15). -/
theorem T_5_extracted {a d : ℝ} (T : ℕ → ℝ) : T 1 = 2 / 3 → T 9 = 4 / 5 → T 5 = 11 / 15 := sorry

Goal:
(((2*n) * (2*n + 2) * (2*n + 4)) / 8) = 32736. -/
theorem even_prod_div_eight_extracted (n : ℕ) : (2 * n) ^ 2 + (2 * n + 2) ^ 2 + (2 * n + 4) ^ 2 = 12296 → ((2 * n) * (2 * n + 2) * (2 * n + 4)) / 8 = 32736 := sorry

/-- Assumptions:
Let n be a natural number.
Define S1 : ℕ → ℕ by S1(n) = (sum for k in the set {0, ..., (n - 1)} of (k^3)).
Define S2 : ℕ → ℕ by S2(n) = (sum for k in the set {0, ..., (n - 1)} of k).
Goal:
S1(n) = (S2(n))^2. -/
theorem sum_cube_of_sum_range_tac_7488 (n : ℕ) (S1 : ℕ → ℕ) (S2 : ℕ → ℕ) (h₁ : S1 n = ∑ k ∈ range n, k ^ 3) (h₂ : S2 n = ∑ k ∈ range n, k) : S1 n = (S2 n) ^ 2 := sorry

Goal:  
n = 502. -/
theorem n_eq_502 (x : ℝ) (a₁ a₂ a₃ : ℝ) (d : ℝ) (n : ℕ) (a : ℕ → ℝ) :
  a₁ = 2 * x - 3 ∧ a₂ = 5 * x - 11 ∧ a₃ = 3 * x + 1 ∧ a₂ - a₁ = d ∧ a₃ - a₂ = d ∧ a n = 2009 → n = 502  :=  by sorry

/-- Assumptions:  
Define m = 2009.  
Define a = 2010.  
Define b = 4018.  
Let n be a natural number.  
Define S = (a + (a+1) + ... + b).  
Goal:  
S mod m = 0. -/
theorem mod_eq_zero (m a b : ℕ) (n : ℕ) (S : ℕ) (h₁ : m = 2009) (h₂ : a = 2010) (h₃ : b = 4018) (h₄ : S = (a + (a+1) + ... + b)) : S % m = 0 := sorry

/-- Assumptions:
Define ℕ as the set of positive integers.
Define f : ℕ × ℕ → ℕ.
For every natural number x, define f(x, x) = x.
For every natural number x and every natural number y, define f(x, y) = f(y, x).
For every natural number x and every natural number y, define ((x + y) * f(x, y)) = (y * f(x, x + y)).
Goal:
f(14, 52) = 364. -/
theorem f_14_52 : f 14 52 = 364 := sorry

/-- Assumptions:
Define a = 121.
Define b = 122.
Define c = 123.
Goal:
The remainder when ((a * b) * c) is divided by 4 is 2. -/
theorem remainder_of_multiplication_by_4_extracted : (121 * 122 * 123) % 4 = 2 := sorry

Goal:
((x = 1) AND (y = 1)) OR ((x = 16) AND (y = 2)) OR ((x = 27) AND (y = 3)). -/
theorem x_eq_one_and_y_eq_one_or_x_eq_16_and_y_eq_2_or_x_eq_27_and_y_eq_3 (hx : 0 < x) (hy : 0 < y) (h : x^(y^2) = y^x) : (x = 1 ∧ y = 1) ∨ (x = 16 ∧ y = 2) ∨ (x = 27 ∧ y = 3) := sorry

Goal:
(9 / (x + y + z)) ≤ ((2 / (x + y)) + (2 / (y + z)) + (2 / (z + x))). -/
theorem nine_div_sum_le_sum_of_pos {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
  9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x)  :=  by sorry

/-- Assumptions:
Define p : ℝ.
Assume (0 < p) ∧ (p < 15).
Define f : ℝ → ℝ by f(x) = |x - p| + |x - 15| + |x - (p + 15)|.
Goal:
The minimum value of f(x) for x in the set {x in ℝ | (p ≤ x) ∧ (x ≤ 15)} is 15. -/
theorem min_displacement_p_15_p_15_p (p : ℝ) (hp_pos : 0 < p) (hp_lt_15 : p < 15) :
  IsLeast {x | p ≤ x ∧ x ≤ 15} (p + 15) := sorry

Goal:
The sum of the coordinates of point A is 4. -/
theorem sum_coordinates_of_A_is_4 (A : ℝ × ℝ) (h₁ : 3 * A.2 = A.1) (h₂ : 2 * A.1 + 5 * A.2 = 11) : A.1 + A.2 = 4 := sorry

/-- Assumptions:
Define f : ℝ → ℝ by f(x) = (c * (x^3)) - (9 * x) + 3.
Define x = 2.
Assume f(2) = 9.
Goal:
c = 3. -/
theorem c_eq_3 (f : ℝ → ℝ) (x : ℝ) (c : ℝ) (h₁ : f = fun x => c * x ^ 3 - 9 * x + 3) (h₂ : x = 2) (h₃ : f 2 = 9) : c = 3 := sorry

Goal:  
The size of the set {x in ℤ | |x - 2| ≤ a} = 11. -/
theorem set_size_eq_11 : (Finset.filter (fun x : ℤ => abs (x - 2) ≤ 5.6) Finset.univ).card = 11 := sorry

Goal:  
The size of the set {m in ℕ | m > 0 and there exists a positive integer n such that (m * n) ≤ (m + n)} is infinite. -/
theorem infinite_setOf_mul_le_add {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m * n ≤ m + n) :
    {m : ℕ | 0 < m ∧ ∃ n : ℕ, 0 < n ∧ m * n ≤ m + n}.Infinite := sorry

/-- Assumptions:
Let x be an integer.
Let y be an integer.
Goal:
NOT (x^5 = (y^2) + 4). -/
theorem not_x_to_the_power_five_eq_y_squared_add_four (x y : ℤ) : ¬(x^5 = y^2 + 4) := sorry

/-- Assumptions:
Define f : ℝ → ℝ.
For every real number x, define f(x) + f(x - 1) = x^2.
Define f(19) = 94.
Goal:
There exists an integer r such that f(94) = 1000 * k + r for some integer k, and r = 561. -/
theorem exists_int_f_94_eq_k_mul_1000_add_561 (f : ℝ → ℝ) (hf : ∀ x, f x + f (x - 1) = x^2) (h19 : f 19 = 94) : ∃ r : ℤ, f 94 = 1000 * r + 561  :=  by sorry

/-- Assumptions:
Define x as a real number.
Goal:
((x + 1)^2) * x = (x^3) + (2*(x^2)) + x. -/
theorem real_polynomial_expansion (x : ℝ) : ((x + 1)^2) * x = x^3 + (2 * (x^2)) + x := sorry

/-- Assumptions:
Define a = 5.
Define b = 3.
Goal:
b^a = 243. -/
theorem ba_eq_243 : (3 : ℝ) ^ (5 : ℕ) = 243 := sorry

/-- Assumptions:
Define f : ℝ → ℝ.
Define h : ℝ → ℝ.
Assume for all real numbers x, h(x) = f⁻¹(x).
Assume h(2) = 10.
Assume h(10) = 1.
Assume h(1) = 2.
Goal:
f(f(10)) = 1. -/
theorem f_f_10 : f (f 10) = 1 := sorry

/-- Assumptions:
Define n = 100.
Define S : ℕ → ℤ by S(k) = sum_{i in the set {0, ..., k}} (2^i).
Goal:
The remainder when S(n) is divided by 7 is 3. -/
theorem remainder_of_sum_two_pow_nat_mod_seven (n : ℕ) (hn : n = 100) (S : ℕ → ℤ)
    (hS : S = fun k => ∑ i in Finset.range (k + 1), 2 ^ i) :
    S n % 7 = 3 := sorry

/-- Assumptions:
Define n = 98.
Let a be a function from ℕ to ℝ.
Assume a is an arithmetic progression.
Define d = 1.
For every natural number k, define a(k+1) = a(k) + d.
Define S = a(1) + a(2) + a(3) + ... + a(n).
Assume S = 137.
Goal:
The sum a(2) + a(4) + a(6) + ... + a(98) = 93. -/
theorem sum_even_index_of_arithmetic_progression (n : ℕ) (a : ℕ → ℝ) (d : ℝ) (h : ∀ k, a (k + 1) = a k + d) (h_sum : ∑ k in Finset.range n, a k = 137) : ∑ k in Finset.range (n/2), a (2 * k + 2) = 93  :=  by sorry

/-- Assumptions:
Define V : ℂ = (1 + i).
Define Z : ℂ = (2 - i).
Goal:
There exists a complex number I such that V = (I * Z) and I = ((1/5) + ((3/5) * i)). -/
theorem exists_I_eq_and_V_eq_I_mul_Z : ∃ I, I = (1/5 + (3/5)*I) ∧ V = I * Z := sorry

/-- Assumptions:
Let p be an integer.
Let q be an integer.
Let r be an integer.
Assume (1 < p) and (p < q) and (q < r).
Assume there exists an integer k such that ((p * q * r) - 1) = ((p - 1) * (q - 1) * (r - 1)) * k.
Goal:
((p = 2) and (q = 4) and (r = 8)) or ((p = 3) and (q = 5) and (r = 15)). -/
theorem abc_conjecture_helper : ∀ p q r : ℤ, 1 < p ∧ p < q ∧ q < r → (p * q * r - 1) = (p - 1) * (q - 1) * (r - 1) * ∃ k, k = 1 → p = 2 ∧ q = 4 ∧ r = 8 ∨ p = 3 ∧ q = 5 ∧ r = 15 := sorry

Goal:
(0 ≤ a) ∧ (a ≤ (1/3)) ∧ ((1/3) ≤ b) ∧ (b ≤ 1) ∧ (1 ≤ c) ∧ (c ≤ (4/3)). -/
theorem constraints_a_b_c_of_a_le_b_le_c_of_a_add_b_add_c_eq_two_of_ab_add_bc_add_ca_eq_one (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (h : a + b + c = 2) (h' : a * b + b * c + c * a = 1) : (0 ≤ a ∧ a ≤ 1 / 3) ∧ 1 / 3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4 / 3 := sorry

Goal:  
((n + m) / (n - m)) = (5 / 3). -/
theorem new_goal_here (a b n m : ℝ) (ha : a = 2014) (hb : b = 2012) (hn : n = 2^a) (hm : m = 2^b) : (n + m) / (n - m) = 5 / 3 := sorry

Goal:  
(a * b * c) = 720. -/
theorem abc_720_of_ab_plus_ac_eq_152_of_bc_plus_ba_eq_162_of_ca_plus_cb_eq_170 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * (b + c) = 152) (hbc : b * (c + a) = 162) (hca : c * (a + b) = 170) : a * b * c = 720 := sorry

/-- Assumptions:  
Define ligs = ℕ.  
Define lags = ℕ.  
Define lugs = ℕ.  
Assume for every natural number x, (7 * x) ligs = (4 * x) lags.  
Assume for every natural number y, (9 * y) lags = (20 * y) lugs.  
Goal:  
There exists a natural number z such that (z * 80) lugs = (63 * z) ligs. -/
theorem exists_multiple_eq_extracted {lags ligs lugs : ℕ → ℕ} : (∀ (x : ℕ), 7 * x * ligs x = 4 * x * lags x) → (∀ (y : ℕ), 9 * y * lags y = 20 * y * lugs y) → ∃ z, z * 80 * lugs z = 63 * z * ligs z := sorry

/-- Assumptions:
Let x be a real number.
Let y be a real number.
Define A = 7.
Define G = sqrt(19).
Assume ((x + y) / 2) = A.
Assume sqrt((x * y)) = G.
Goal:
(x^2 + y^2) = 158. -/
theorem x_sq_add_y_sq_eq_158 {x y : ℝ} (A : ℝ) (G : ℝ) (hA : A = 7) (hG : G = Real.sqrt 19) (hxy : (x + y) / 2 = A) (hxy' : Real.sqrt (x * y) = G) : x ^ 2 + y ^ 2 = 158 := sorry

Goal:
n = 5. -/
theorem n_eq_5 : n = 5 := sorry

Goal:
(a + b) = (8 / 3). -/
theorem a_add_b_eq_of_a_sq_mul_b_cub_eq_div_of_a_div_b_cub_eq_div (a b : ℝ) (h₁ : a ^ 2 * b ^ 3 = 32 / 27) (h₂ : a / b ^ 3 = 27 / 4) : a + b = 8 / 3 := sorry

/-- Assumptions:
Define a = 3.
Define b = 11.
Define the function ⋆ : ℝ × ℝ → ℝ by ⋆(x, y) = ((1 / y) - (1 / x)) / (x - y).
Goal:
⋆(3, 11) = 1 / 33. -/
theorem star_apply_3_11 : star (3 : ℝ) 11 = 1 / 33 := sorry

/-- Assumptions:
Define b = 9.
Define n = 852.
Goal:
n = 695. -/
theorem example_extracted (b : ℕ) (n : ℕ) : n = 695 := sorry

/-- Assumptions:
Let a be an integer.
Assume a is odd.
Let b be a natural number.
Assume 4 divides b.
Goal:
(a^2 + b^2) ≡ 1 mod 8. -/
theorem sq_add_sq_mod_eight_of_odd_of_dvd (a : ℤ) (b : ℕ) (ha : Odd a) (hb : 4 ∣ b) :
  a ^ 2 + b ^ 2 ≡ 1 [ZMOD 8] := sorry

/-- Assumptions:
Define a = 15.
Define b = 85.
Define d = 20.
Goal:
The size of the set {x in ℤ | (a ≤ x) ∧ (x ≤ b) ∧ (There exists an integer k such that x = d * k)} = 4. -/
theorem card_fintype_ext :
  Fintype.card { x : ℤ // 15 ≤ x ∧ x ≤ 85 ∧ ∃ k, x = 20 * k } = 4 := sorry

/-- Assumptions:
Define f : ℕ⁺ → ℕ⁺.
For every natural number n ≥ 1, assume f(n+1) > f(f(n)).
Goal:
For every natural number n ≥ 1, f(n) = n. -/
theorem f_eq_n_forall_of_one_le {f : ℕ → ℕ} (hf : ∀ n ≥ 1, f (f n) < f (n + 1)) : ∀ n ≥ 1, f n = n := sorry

Goal:
A ≡ (2^m) mod M. -/
theorem A_modEq_M_def {n : ℕ} (hn : 0 < n) : (3^(2^n) - 1) ≡ 2^(n + 2) [MOD 2^(n + 3)] := sorry

Goal:  
The size of the set {x in I | f(x) = g(x)} = 2. -/
theorem sin_pi_div_two_cos_eq_cos_pi_div_two_sin_tac_26311 (x : ℝ) (hx : x ∈ Icc 0 π) : {x | x ∈ Icc 0 π ∧ sin (π / 2 * cos x) = cos (π / 2 * sin x)}.Subsingleton := sorry

/-- Assumptions:
Define a ∈ ℝ.
Define f : ℝ → ℝ by f(x) = √(4 + √(16 + 16*x)).
Define g : ℝ → ℝ by g(x) = √(1 + √(1 + x)).
Assume (f(a) + g(a)) = 6.
Goal:
a = 8. -/
theorem real_8_plus_real_16_eq_6_plus_real_8 (a : ℝ) (f g : ℝ → ℝ) (hf : ∀ x, f x = Real.sqrt (4 + Real.sqrt (16 + 16 * x))) (hg : ∀ x, g x = Real.sqrt (1 + Real.sqrt (1 + x))) : f a + g a = 6 → a = 8 := sorry

/-- Assumptions:
Define x as a real number.
Goal:
((x + 3) * ((2 * x) - 6)) = ((2 * (x^2)) - 18). -/
theorem t10203 (x : ℝ) : (x + 3) * (2 * x - 6) = 2 * x ^ 2 - 18 := sorry

/-- Assumptions:
Define an arithmetic sequence a : ℕ → ℝ.
Define d ∈ ℝ.
Assume for every natural number n, a(n) = a(0) + (n * d).
Assume a(6) = 30.
Assume a(10) = 60.
Goal:
a(20) = 135. -/
theorem a_20_extracted {a : ℕ → ℝ} {d : ℝ} : (∀ (n : ℕ), a n = a 0 + n * d) → a 6 = 30 → a 10 = 60 → a 20 = 135 := sorry

Goal:
(2*n) = 8. -/
theorem even_integer_sum_eq_odd_sum_minus_four (n : ℤ) : (2 * n) = 8  :=  by sorry

/-- Assumptions:
Define x as a real number.
Assume ((x - 9) / (x + 1)) = 2.
Goal:
x = -11. -/
theorem x_eq_minus_11 (x : ℝ) (h : (x - 9) / (x + 1) = 2) : x = -11 := sorry

/-- Assumptions:
Define S = 25.
Define D = 11.
Let x be a real number.
Let y be a real number.
Assume (x + y) = S.
Assume (x - y) = D.
Goal:
The larger of the two numbers is 18. -/
theorem max_of_add_eq_S_sub_eq_D (x y : ℝ) (h₁ : x + y = 25) (h₂ : x - y = 11) : max x y = 18 := sorry

Goal:
For every integer i in the set {1, ..., n}, x_i = 0. -/
theorem x_eq_zero_of_sum_eq_zero (n : ℕ) (hn : n = 3) (a : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (ha : ∀ i, a i i > 0) (h : ∀ i j, i ≠ j → a i j < 0) (h2 : ∀ i, 0 < ∑ j, a i j)
    (h3 : ∀ i, ∑ j, a i j * x j = 0) : ∀ i, x i = 0 := sorry

/-- Assumptions:
Let n be an integer.
Assume (3 * n) ≡ 2 mod 11.
Goal:
n ≡ 8 mod 11. -/
theorem example_extracted {n : ℤ} : 3 * n ≡ 2 [ZMOD 11] → n ≡ 8 [ZMOD 11] := sorry

Goal:
(1 + (n * x)) ≤ ((1 + x)^n). -/
theorem one_add_mul_le_pow {x : ℝ} (hx : -1 < x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n := sorry

/-- Assumptions:
Define n = 1529.
Define m = 6.
Goal:
There exists an integer q and an integer r such that (n = (m * q) + r) and (0 ≤ r) and (r < m) and (r = 5). -/
theorem exists_eq_mul_add_of_dvd_add_of_lt_tac_1529 (n m : ℕ) (hn : n = 1529) (hm : m = 6) : ∃ q r, n = m * q + r ∧ 0 ≤ r ∧ r < m ∧ r = 5 := sorry

Goal:
k = 18. -/
theorem k_eq_18 (n : ℕ) (m : ℕ) (k : ℕ) (h₁ : m = 2 * n) (h₂ : k = m + 2) (h₃ : m * k = 288) : k = 18 := sorry

/-- Assumptions:
Define a = 35.
Define b = 40.
Define c = 1400.
Assume a * b = c.
Define m = 1399.
Assume m is a natural number.
Define k = 160.
Assume k is an integer.
Goal:
There exists an integer n such that (0 ≤ n) and (n < m) and (There exists an integer q such that (k * n) = (m * q) + 1). -/
theorem exists_n_lem (a b c : ℕ) (ha : a = 35) (hb : b = 40) (hc : c = 1400) (habc : a * b = c) (m : ℕ) (hm : m = 1399) (k : ℤ) (hk : k = 160) : ∃ n, 0 ≤ n ∧ n < m ∧ ∃ q, ↑k * n = ↑m * q + 1 := sorry

Goal:  
p + q = 929. -/
theorem p_add_q_eq_929 (a : ℝ) (p q : ℤ) (hp : 0 < p) (hq : 0 < q) (hgcd : Nat.Coprime p.natAbs q.natAbs) (h : ∀ x : ℝ, (Int.floor x * (x - Int.floor x)) = a * (x^2) → ∑ k in Finset.range 1000, (Int.floor (a * (↑k)^2)) = 420) : p + q = 929 := sorry

/-- Assumptions:
Define a = 1342.
Define b = 13.
Let r be an integer.
Assume r is the remainder when a is divided by b.
Define r = a mod b.
Let n be a natural number.
Assume n > 0.
Assume n is a multiple of a.
Assume there exists an integer q such that n = a * q.
Assume the remainder when n is divided by b is smaller than r.
Goal:
n = 6710. -/
theorem n_eq_6710 : n = 6710 := sorry

/-- Assumptions:  
Define θ as a real number.  
Assume 0 < θ ≤ 2π.  
Define f : ℝ → ℝ by f(θ) = 1 - (3 * sin(θ)) + (5 * cos(3 * θ)).  
Goal:  
The size of the set {θ in ℝ | (0 < θ) ∧ (θ ≤ 2π) ∧ (f(θ) = 0)} = 6. -/
theorem card_zero_of_f_eq_zero :
  {θ : ℝ | 0 < θ ∧ θ ≤ 2 * π ∧ (1 - 3 * Real.sin θ + 5 * Real.cos (3 * θ) = 0)}.card = 6 := sorry

/-- Assumptions:
Define f : ℝ → ℝ by f(x) = |(2 - x)|.
Assume for all real numbers x, f(x) = 3.
Goal:
The sum of the set {x in ℝ | f(x) = 3} = 4. -/
theorem sum_set_of_abs_sub_two_eq_three (f : ℝ → ℝ) (hf : ∀ x, f x = |(2 - x)|) : ∑' x : ℝ, x ∈ {x : ℝ | f x = 3} → x = 4 := sorry

Goal:
There exists an integer s such that expression = s^2. -/
theorem ∃ s : ℤ, (n + 2)! - (n + 1)! - n! = s^2 := sorry

Goal:  
a_1 + b_1 = 1 / (2^98). -/
theorem a_1_add_b_1_eq_1_div_2_pow_98 : a_1 + b_1 = 1 / (2 ^ 98) := sorry

/-- Assumptions:
Let n be a natural number.
Define a_1, a_2, ..., a_n as real numbers.
Define f : ℝ → ℝ by f(x) = cos(a_1 + x) + (1/2) * cos(a_2 + x) + (1/4) * cos(a_3 + x) + ... + (1/(2^(n-1))) * cos(a_n + x).
Define x_1 as a real number.
Define x_2 as a real number.
Assume f(x_1) = 0.
Assume f(x_2) = 0.
Goal:
There exists an integer m such that (x_2 - x_1) = m * π. -/
theorem cos_n_eq_zero_extracted (n : ℕ) (a : Fin n → ℝ) (f : ℝ → ℝ) (x₁ x₂ : ℝ) :
 (∀ (x : ℝ), f x = ∑ i : Fin n, (↑(2^(1 - i)))⁻¹ * Real.cos (a i + x)) →
 f x₁ = 0 → f x₂ = 0 → ∃ m, x₂ - x₁ = ↑m * Real.pi := sorry

/-- Assumptions:
Define S = {n in ℕ | 0 ≤ n ≤ 50 and there exists an integer k such that n = 3*k}.
Define f : ℕ → ℕ by f(n) = n mod 10.
Goal:
The sum of f(n) for n in the set S is 78. -/
theorem sum_apply_eq_78 : ∑ n in filter (fun n => ∃ k : ℤ, n = 3 * k) (Finset.Icc 0 50), n % 10 = 78  :=  by sorry

/-- Assumptions:
Define i as the imaginary unit such that i^2 = -1.
Goal:
((i / 2))^2 = (-1 / 4). -/
theorem sq_div_two_extracted : (Complex.I / 2) ^ 2 = (-1 / 4) := sorry

/-- Assumptions:
Define B_x = 7.
Define B_y = -1.
Define C_x = -1.
Define C_y = 7.
Define m : ℝ.
Define b : ℝ.
Assume for every real number x, the point (x, (m*x + b)) lies on line ℓ.
Assume (B_x, B_y) lies on line ℓ.
Assume (C_x, C_y) lies on line ℓ.
Goal:
(m + b) = 5. -/
theorem slope_intercept_eq_five (B_x B_y C_x C_y m b : ℝ) (h₁ : B_x = 7) (h₂ : B_y = -1) (h₃ : C_x = -1) (h₄ : C_y = 7) (h₅ : ∀ x, (x, m*x + b) ∈ ℓ) (h₆ : (B_x, B_y) ∈ ℓ) (h₇ : (C_x, C_y) ∈ ℓ) : m + b = 5 := sorry

Goal:
f(84) = 997. -/
theorem f_84 : f 84 = 997 := sorry

/-- Assumptions:
Define d₁ = 3.
Define w₁ = 1.5.
Define d₂ = 10.
Assume d₁, d₂, w₁ are positive real numbers.
Assume the rate of water consumption is constant.
Goal:
There exists a real number w₂ such that w₂ = ((w₁) / (d₁)) * (d₂). -/
theorem water_consumption_constant_extracted (d₁ d₂ w₁ : ℝ) : 0 < d₁ → 0 < d₂ → 0 < w₁ → ∃ w₂, w₂ = w₁ / d₁ * d₂ := sorry

/-- Assumptions:
Let a be an integer.
Let b be an integer.
Goal:
There exists an integer a and there exists an integer b such that NOT ( (a is even AND b is even) if and only if (There exists an integer k such that (a^2 + b^2) = 8 * k) ). -/
theorem exists_sq_add_sq_eq_eight_mul_extracted {a b : ℤ} : ¬(Even a ∧ Even b) ↔ ∃ k, a ^ 2 + b ^ 2 = 8 * k := sorry

Goal:
(a + b) = √5. -/
theorem a_add_b_eq_sqrt_five (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (h₁ : a - 1/a = 1) (h₂ : b - 1/b = 1) : a + b = √5 := sorry

/-- Assumptions:
Define n = 9.
Let k be a natural number.
Define S : ℕ → ℕ by S(n) = Σ_{k in the set {1, ..., n}} (k^2).
Goal:
The units digit of S(9) is 5. -/
theorem units_digit_of_S_9 : (∑ k in Finset.Icc 1 9, k^2).unitsDigit = 5 := sorry

Goal:  
n = 41. -/
theorem n_eq_41 (n : ℤ) (hn : 0 < n) (d : ℤ) (hd : d > 1) (h1 : d ∣ (n^2 - n + 41)) (h2 : d ∣ ((n + 1)^2 - (n + 1) + 41)) : n = 41 := sorry

