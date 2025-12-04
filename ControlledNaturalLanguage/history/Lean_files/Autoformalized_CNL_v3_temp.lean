
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
    (hlt : 0 < a ∧ a < b ∧ b < c ∧ c < d) (hmul : a * d = b * c) (k m : ℤ) 
    (had : a + d = 2 ^ k) (hbc : b + c = 2 ^ m) : a = 1 := sorry

theorem abs_sum_inequality (a b : ℝ) : |a + b| / (1 + |a + b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := sorry

theorem multiplicative_inverse_condition : ∃ n : ℤ, 0 ≤ n ∧ n < 1399 ∧ (n * 160) % 1399 = 1 ∧ n = 1058 := sorry

theorem not_prime_of_conditions (K L M N : ℕ) (h1 : K > L) (h2 : L > M) (h3 : M > N) 
    (h4 : K * M + L * N = (K + L - M + N) * (-K + L + M + N)) : 
    ¬ Nat.Prime (K * L + M * N) := sorry

theorem inequality_for_positive_reals : ∀ (x y z : ℝ), x > 0 → y > 0 → z > 0 → 9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := sorry

theorem exists_integer_satisfying_congruences : ∃ (n : ℤ), 2 * n ≡ 15 [ZMOD (47 : ℤ)] ∧ n ≡ 31 [ZMOD (47 : ℤ)] := sorry

theorem mod_goal : ∀ (b : ℤ), (24 * b) ≡ 1 [ZMOD (11 : ℤ)^2] → b = 116 := sorry

theorem linear_system_solution (x y z : ℝ) (h1 : 3 * x + y = 17) (h2 : 5 * y + z = 14) (h3 : 3 * x + 5 * z = 41) : x + y + z = 12 := sorry

theorem goal_statement : f (f (f (f (f 4)))) = 1 := sorry

where

def f (n : ℤ) : ℤ :=
  if n % 2 = 0 then n ^ 2 - 4 * n - 1 else n ^ 2

theorem perfect_square_div_factorial (n : ℤ) (hn : n ≥ 9) : ∃ (k : ℤ), ((Nat.factorial (n + 2) : ℤ) - (Nat.factorial (n + 1) : ℤ)) / (Nat.factorial n : ℤ) = k ^ 2 := sorry

theorem exist_irrational_power_rational : ∃ (a b : ℝ), Irrational a ∧ Irrational b ∧ Rational (a ^ b) := sorry

theorem smallest_k_satisfies_conditions : ∃ k : ℕ, 0 < k ∧ (∀ n : ℕ, 0 < n → 
    let a := 6 * n + k
    let b := 6 * n + 3
    let c := 6 * n + 2
    let d := 6 * n + 1 in
    Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime a d) ∧
    (∀ k' : ℕ, 0 < k' → k' < k → ¬∀ n : ℕ, 0 < n → 
        let a := 6 * n + k'
        let b := 6 * n + 3
        let c := 6 * n + 2
        let d := 6 * n + 1 in
        Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime a d) := sorry

theorem count_four_digit_even_divisible_by_five : 
    let digits := Finset.filter (fun n : ℕ => 1000 ≤ n ∧ n ≤ 9999 ∧ (∀ d : ℕ, d ∈ (Nat.digits 10 n) → Even d) ∧ 5 ∣ n) Finset.univ in
    Finset.card digits = 100 := sorry

theorem product_of_log_sums_eq_21000 : 
    (∑ k in Finset.Icc 1 20, Real.log ((3 : ℝ) ^ (k ^ 2)) / Real.log ((5 : ℝ) ^ k)) * 
    (∑ k in Finset.Icc 1 100, Real.log ((25 : ℝ) ^ k) / Real.log ((9 : ℝ) ^ k)) = 21000 := sorry

theorem sum_reciprocal_sqrt_bound : ∑ k in Finset.Icc 2 10000, 1 / Real.sqrt k < 198 := sorry

theorem smallest_n_with_common_factor :
    let p (n : ℕ) := n ^ 2 - n + 41 in
    (∃ n : ℕ, ∃ d : ℕ, d > 1 ∧ d ∣ p n ∧ d ∣ p (n + 1)) →
    let candidates := Finset.filter (λ n : ℕ => ∃ d : ℕ, d > 1 ∧ d ∣ p n ∧ d ∣ p (n + 1)) (Finset.Icc 0 41) in
    Finset.min' candidates (by
      refine ⟨41, ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by simp, by simp⟩, ?_⟩
      refine ⟨41, ?_⟩
      constructor
      · simp
      constructor
      · simp [p]
      · simp [p]) = 41 := sorry

theorem factor_identity (A B : ℤ) (x : ℝ) (h : 10 * x ^ 2 - x - 24 = (A * x - 8) * (B * x + 3)) : A * B + B = 12 := sorry

theorem inequality_proof (a b : ℝ) (ha : a > 0) (hb : b > 0) (h : b ≤ a) : (a + b)/2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := sorry

theorem count_perfect_square_divisors : 
    let n := ∏ i in Finset.Icc 1 9, Nat.factorial i in
    Fintype.card {d : ℕ | d ∣ n ∧ ∃ (k : ℕ), d = k ^ 2} = 672 := sorry

theorem exists_infinitely_many_m_with_property : Set.Infinite {m : ℕ | m > 0 ∧ ∃ n : ℕ, n > 0 ∧ m * n ≤ m + n} := sorry

theorem complex_identity : I = (1/5 : ℂ) + (3/5 : ℂ) * Complex.I := by
  intro V I Z (hV_eq : V = (1 : ℂ) + Complex.I) (hZ_eq : Z = (2 : ℂ) - Complex.I) (hV_eq2 : V = I * Z)
  rw [hV_eq, hZ_eq] at hV_eq2
  linarith
  done

theorem not_n_gt_84 : ∀ (n : ℕ), n > 0 → (1/2 + 1/3 + 1/7 + 1/(n : ℕ) : ℚ) ∈ Set.range (Int.cast : ℤ → ℚ) → ¬(n > 84) := sorry

theorem remainder_of_5_pow_30_mod_7 : (5 ^ 30) % 7 = 1 := sorry

theorem gcd_lcm_implies_n_eq_70 (n : ℕ) (h1 : Nat.gcd n 40 = 10) (h2 : Nat.lcm n 40 = 280) : n = 70 := sorry

theorem product_expression_equivalence :
    let a : ℝ := 2
    let b : ℝ := 3
    let P : ℕ → ℝ := λ n => ∏ k in Finset.range (n + 1), (a^(2^k) + b^(2^k))
    in P 6 = a^128 - b^128 := sorry

theorem find_coefficients : ∃ (a b c : ℝ), (∀ (x : ℝ), x ^ 3 + a * x ^ 2 + b * x + c = (x - Real.cos (2 * π / 7)) * (x - Real.cos (4 * π / 7)) * (x - Real.cos (6 * π / 7))) ∧ a * b * c = a * b * c := sorry

theorem arithmetic_progression_sum_of_even_terms :
    ∀ (n : ℕ) (a : ℕ → ℝ) (d : ℝ), 
    (∀ k : ℕ, a (k + 1) = a k + d) → 
    d = 1 → 
    (∑ k in Finset.range 98, a (k + 1)) = 137 → 
    (∑ k in Finset.range 49, a (2 * k + 2)) = 93 := sorry

theorem point_satisfies_equation : ∀ (x y : ℝ), 3 * y = x → 2 * x + 5 * y = 11 → x + y = 4 := sorry

theorem prime_divides_a_pow_p_minus_a (p : ℕ) (hp : Nat.Prime p) (a : ℕ) : p ∣ a ^ p - a := sorry

theorem f_negatives : {x : ℚ | x > 0} → Prop := by
  intro f hdomain hmultiplicative hprime
  intro x hx
  have h1 : f (17/32 : ℚ) < 0 := by
    sorry
  have h2 : f (11/16 : ℚ) < 0 := by
    sorry
  have h3 : f (7/9 : ℚ) < 0 := by
    sorry
  have h4 : f (7/6 : ℚ) < 0 := by
    sorry
  have h5 : f (25/11 : ℚ) < 0 := by
    sorry
  exact ⟨h1, h2, h3, h4, h5⟩

theorem f_25_over_11_negative (f : ℚ → ℚ) (hdomain : ∀ x : ℚ, x > 0 → f x = f x)
    (hmultiplicative : ∀ (a b : ℚ), a > 0 → b > 0 → f (a * b) = f a + f b)
    (hprime : ∀ (p : ℕ), Nat.Prime p → f (p : ℚ) = (p : ℚ)) : f (25/11 : ℚ) < 0 := sorry

theorem square_root_condition_implies_a_eq_8 (a : ℝ) 
    (h1 : 16 + 16 * a ≥ 0) (h2 : 1 + a ≥ 0) 
    (h3 : 4 + Real.sqrt (16 + 16 * a) ≥ 0) (h4 : 1 + Real.sqrt (1 + a) ≥ 0) : 
    a = 8 := sorry

theorem inequality_proof (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : a * b + (a - b) ≤ 1 := sorry

theorem floor_sum_eq_3702 : 
    let N : ℝ := 1/3 in
    ∑ i in Finset.Icc 1 4, Int.floor ((10 : ℝ) ^ i * N) = 3702 := sorry

theorem inequality_proof (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) :
    (a ^ 2 / b) + (b ^ 2 / c) + (c ^ 2 / d) + (d ^ 2 / a) ≥ a + b + c + d := sorry

theorem natural_numbers_assumption : ∀ (a b c d e f g h i j k l m n o p q r s t u v w x y z A B C D E F G H I J K L M N O P Q R S T U V W X Y Z AA AB AC AD AE AF AG AH AI AJ AK AL AM AN AO AP AQ AR AS AT AU AV AW AX AY AZ BA BB BC BD BE BF BG BH BI BJ BK BL BM BN BO BP BQ BR BS BT BU BV BW BX BY BZ CA CB CC CD CE CF CG CH CI CJ CK CL CM CN CO CP CQ CR CS CT CU CV CW CX CY CZ DA DB DC DD DE DF DG DH DI DJ DK DL DM DN DO DP DQ DR DS DT DU DV DW DX DY DZ EA EB EC ED EE EF EG EH EI EJ EK EL EM EN EO EP EQ ER ES ET EU EV EW EX EY EZ FA FB FC FD FE FF FG FH FI FJ FK FL FM FN FO FP FQ FR FS FT FU FV FW FX FY FZ GA GB GC GD GE GF GG GH GI GJ GK GL GM GN GO GP GQ GR GS GT GU GV GW GX GY GZ HA HB HC HD HE HF HG HH HI HJ HK HL HM HN HO HP HQ HR HS HT HU HV HW HX HY HZ IA IB IC ID IE IF IG IH II IJ IK IL IM IN IO IP IQ IR IS IT IU IV IW IX IY IZ JA JB JC JD JE JF JG JH JI JJ JK JL JM JN JO JP JQ JR JS JT JU JV JW JX JY JZ KA KB KC KD KE KF KG KH KI KJ KK KL KM KN KO KP KQ KR KS KT KU KV KW KX KY KZ LA LB LC LD LE LF LG LH LI LJ LK LL LM LN LO LP LQ LR LS LT LU LV LW LX LY LZ MA MB MC MD ME MF MG MH MI MJ MK ML MM MN MO MP MQ MR MS MT MU MV MW MX MY MZ NA NB NC ND NE NF NG NH NI NJ NK NL NM NN NO NP NQ NR NS NT NU NV NW NX NY NZ OA OB OC OD OE OF OG OH OI OJ OK OL OM ON OO OP OQ OR OS OT OU OV OW OX OY OZ PA PB PC PD PE PF PG PH PI PJ PK PL PM PN PO PP PQ PR PS PT PU PV PW PX PY PZ QA QB QC QD QE QF QG QH QI QJ QK QL QM QN QO QP QQ QR QS QT QU QV QW QX QY QZ RA RB RC RD RE RF RG RH RI RJ RK RL RM RN RO RP RQ RR RS RT RU RV RW RX RY RZ SA SB SC SD SE SF SG SH SI SJ SK SL SM SN SO SP SQ SR SS ST SU SV SW SX SY SZ TA TB TC TD TE TF TG TH TI TJ TK TL TM TN TO TP TQ TR TS TT TU TV TW TX TY TZ UA UB : ℕ), True := sorry

theorem sin_eq_cos_solutions : ∃! (x : ℝ), x ∈ Set.Icc (0 : ℝ) π ∧ sin ((π/2) * cos x) = cos ((π/2) * sin x) := sorry

theorem maximum_value_of_f : 
    IsMaxOn (fun (t : ℝ) => ((Real.rpow 2 t - 3 * t) * t) / (Real.rpow 4 t)) Set.univ (1/12) := sorry

theorem minimize_quadratic : IsMinOn (fun (x : ℝ) => x ^ 2 - 14 * x + 3) Set.univ 7 := sorry

theorem largest_sum_of_factors_of_2001 :
    ∀ (I M O : ℕ) (hI : I > 0) (hM : M > 0) (hO : O > 0) (hdistinct : I ≠ M ∧ I ≠ O ∧ M ≠ O) 
    (hprod : I * M * O = 2001), 
    I + M + O ≤ 671 ∧ ∃ (I' M' O' : ℕ) (hI' : I' > 0) (hM' : M' > 0) (hO' : O' > 0) 
    (hdistinct' : I' ≠ M' ∧ I' ≠ O' ∧ M' ≠ O') (hprod' : I' * M' * O' = 2001), 
    I' + M' + O' = 671 := sorry

theorem tan_eq_cos_solutions : 
    let solutions : Set ℝ := {x | x ∈ Set.Icc (0 : ℝ) (2 * π) ∧ Real.tan (2 * x) = Real.cos (x / 2)}
    in Finset.card (solutions.toFinite.toFinset) = 5 := sorry

theorem least_sum_of_m_n : ∃ (m n : ℕ), 0 < m ∧ 0 < n ∧ Nat.gcd m n = 8 ∧ Nat.lcm m n = 112 ∧ m + n = 72 ∧ ∀ (x y : ℕ), 0 < x ∧ 0 < y ∧ Nat.gcd x y = 8 ∧ Nat.lcm x y = 112 → 72 ≤ x + y := sorry

theorem sum_final_three_digits_of_5_pow_100_eq_13 : 
    let n : ℕ := 100 in
    let digits := (5^n).digits in
    let final_three := if digits.length < 3 then digits else digits.take 3 in
    final_three.sum = 13 := sorry

theorem sequence_parity : 
    let D : ℕ → ℤ := fun
      | 0 => 0
      | 1 => 0
      | 2 => 1
      | n + 3 => D (n + 2) + D n
    in Even (D 2021) ∧ Odd (D 2022) ∧ Even (D 2023) := sorry

theorem n_root_n_le_two_minus_one_over_n (n : ℕ) (hn : n > 0) : (n : ℝ) ^ ((1 : ℝ) / (n : ℝ)) ≤ 2 - (1 : ℝ) / (n : ℝ) := sorry

theorem product_abc_eq_720 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a * (b + c) = 152) (h2 : b * (c + a) = 162) (h3 : c * (a + b) = 170) :
    a * b * c = 720 := sorry

theorem remainder_of_1529_div_by_6_is_5 : (1529 : ℕ) % (6 : ℕ) = 5 := sorry

theorem square_of_ninety_one : (91 : ℤ) ^ 2 = 8281 := sorry

theorem log_base_3_of_27_eq_3 : Real.logb 3 (27 : ℝ) = (3 : ℝ) := sorry

theorem non_zero_real_equals_neg_two (a : ℝ) (h : a ≠ 0) : a = -2 := sorry

theorem complex_equation_implies_sum (z : ℂ) (h : 12 * ‖z‖^2 = 2 * ‖z + 2‖^2 + ‖z^2 + 1‖^2 + 31) : z + 6 / z = -2 := sorry

theorem arithmetic_geometric_means_square_sum :
    ∀ (x y : ℝ), x ≥ 0 → y ≥ 0 → (x + y) / 2 = 7 → Real.sqrt (x * y) = Real.sqrt 19 → x ^ 2 + y ^ 2 = 158 := sorry

theorem cube_root_identity (r : ℝ) (h : r ≠ 0) (h1 : r^(1/3 : ℝ) + 1 / (r^(1/3 : ℝ)) = 3) : r^3 + 1 / r^3 = 5778 := sorry

theorem exists_unique_initial_value : ∃! (x₁ : ℝ), ∀ (n : ℕ), let x := Nat.rec x₁ (λ k xₖ => xₖ * (xₖ + 1 / (k : ℝ))) n in 0 < x ∧ x < Nat.rec x₁ (λ k xₖ => xₖ * (xₖ + 1 / (k : ℝ))) (n + 1) ∧ Nat.rec x₁ (λ k xₖ => xₖ * (xₖ + 1 / (k : ℝ))) (n + 1) < 1 := sorry

theorem greatest_distance_between_sets :
    let A : Set ℂ := {z | z ^ 3 - 8 = 0}
    let B : Set ℂ := {z | z ^ 3 - 8 * z ^ 2 - 8 * z + 64 = 0}
    sSup {d | ∃ a ∈ A, ∃ b ∈ B, d = Complex.dist a b} = 2 * Real.sqrt 21 := sorry

theorem div_lemma (n : ℕ) : 11 ∣ (10^n - (-1 : ℤ)^n) := sorry

theorem product_bound (n : ℕ) (a : ℕ → ℝ) (h_nonneg : ∀ i, 1 ≤ i → i ≤ n → 0 ≤ a i) (h_sum : ∑ i in Finset.Icc 1 n, a i = n) : 
    ∏ i in Finset.Icc 1 n, a i ≤ 1 := sorry

theorem log_squared_eq_twenty (x : ℝ) (y : ℝ) (hx_pos : x > 0) (hx_ne_one : x ≠ 1) (hy_pos : y > 0) (hy_ne_one : y ≠ 1)
    (h_log_eq : Real.logb 2 x = Real.logb y 16) (h_product : x * y = 64) : (Real.logb 2 (x / y)) ^ 2 = 20 := sorry

theorem solve_for_c (c x : ℝ) (h : f c x = 9) (h2 : x = 2) : c = 3 := sorry

theorem inequality_proof : ∀ (x : ℝ) (n : ℕ), x > -1 → (1 + n * x) ≤ (1 + x) ^ n := sorry

theorem mod_problem : ∃ n : ℤ, 0 ≤ n ∧ n < 101 ∧ 123456 ≡ n [ZMOD 101] ∧ n = 34 := sorry

theorem son_age_six (f s : ℕ) (h1 : f = 5 * s) (h2 : (f - 3) + (s - 3) = 30) : s = 6 := sorry

theorem arithmetic_series_proof (a d : ℝ) (n : ℕ) (S_n : ℕ → ℝ) 
    (h_formula : ∀ n, S_n n = (n : ℝ) / 2 * (2 * a + ((n : ℝ) - 1) * d)) 
    (h_S5 : S_n 5 = 70) (h_S10 : S_n 10 = 210) : a = 42/5 := sorry

theorem residue_mod_four : (121 : ℤ) * 122 * 123 % 4 = 2 := sorry

theorem sum_first_twelve_mod_four_eq_two : (Finset.sum (Finset.range 12) fun n : ℕ => n) % 4 = 2 := sorry

theorem expression_evaluation : ∀ (x : ℝ), x = 4 → (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * 4 * x + 1 = 11 := sorry

theorem sum_of_solutions_eq_four : ∃ (solutions : Set ℝ), (∀ (x : ℝ), x ∈ solutions ↔ |2 - x| = 3) ∧ ∑ x in solutions, x = 4 := sorry

theorem product_of_real_roots_eq_20 :
    ∃ (roots : Set ℝ), (∀ (x : ℝ), x ∈ roots ↔ x^2 + 18*x + 30 = 2 * Real.sqrt (x^2 + 18*x + 45) ∧ x^2 + 18*x + 45 ≥ 0) ∧
    (∏ x in roots.toFinset, x) = 20 := sorry

theorem f_of_three_eq_eight (a b : ℝ) (f : ℝ → ℝ) (h : ∀ x, f x = a * x ^ 4 - b * x ^ 2 + x + 5) (h2 : f (-3) = 2) : f 3 = 8 := sorry

theorem positive_integer_solution :
    ∀ (a b c d : ℕ),
      0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
      a * b * c * d = 40320 ∧
      a * b + a + b = 524 ∧
      b * c + b + c = 146 ∧
      c * d + c + d = 104 →
      a - d = 10 := sorry

theorem base_three_conversion : (Nat.ofDigits 3 [1, 2, 2, 2] : ℕ) = 53 := sorry

theorem remainder_property (n : ℕ) (hn : n > 0) : (3^(2^n) - 1) % (2^(n + 3)) = 2^(n + 2) := sorry

theorem arithmetic_sequence_term : 
    ∀ (A D : ℝ) (h1 : A + (7 - 1 : ℕ) * D = (30 : ℝ)) (h2 : A + (11 - 1 : ℕ) * D = (60 : ℝ)), 
    A + (21 - 1 : ℕ) * D = (135 : ℝ) := sorry

theorem f_property : f (84 : ℤ) = (997 : ℤ) := sorry

theorem determine_functions : 
    {f : ℤ → ℤ | ∀ (a b : ℤ), f (2 * a) + 2 * f b = f (f (a + b))} = {f | f = 0 ∨ f = fun x => x ∨ f = fun x => -x} := sorry

theorem compute_f_g_at_two : f (g (2 : ℝ)) = (8 : ℝ) := sorry

theorem ordered_pair_is_one_one (a b : ℝ) (h1 : 3 * a + 2 * b = 5) (h2 : a + b = 2) : (a, b) = (1, 1) := sorry

theorem exists_prime_pair_with_specific_property : ∃ (p q : ℕ), Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ p > 4 ∧ p < 18 ∧ q > 4 ∧ q < 18 ∧ (p * q) - (p + q) = 119 ∧ ∀ (p' q' : ℕ), Nat.Prime p' ∧ Nat.Prime q' ∧ p' ≠ q' ∧ p' > 4 ∧ p' < 18 ∧ q' > 4 ∧ q' < 18 ∧ (p' * q') - (p' + q') = 119 → p' = p ∧ q' = q := sorry

theorem marbles_removed_eq_six : R = 6 := sorry

theorem f_14_52_eq_364 : f (14 : ℕ) (52 : ℕ) = (364 : ℝ) := sorry

theorem cube_root_identity : ∀ (a : ℝ), a = 8 → (16 * (Real.rpow a (2/3 : ℝ))) ^ (1/3 : ℝ) = 4 := sorry

theorem radical_simplification (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (60 * x) * Real.sqrt (12 * x) * Real.sqrt (63 * x) = 36 * x * Real.sqrt (35 * x) := sorry

theorem water_distance_relation (d w : ℝ) (h : w = 1.5 ∧ d = 3) : (d = 10 → w = 5) := sorry

theorem number_of_solutions :
    ∀ (θ : ℝ), 0 < θ ∧ θ ≤ 2 * π → 
    let equation : Prop := 1 - 3 * Real.sin θ + 5 * Real.cos (3 * θ) = 0
    in Fintype.card {x // equation} = 6 := sorry

theorem log_sqrt_identity (x y a b : ℝ) (ha_pos : a > 0) (ha_ne_one : a ≠ 1) (hb_pos : b > 0) (hb_ne_one : b ≠ 1) 
    (hx_pos : x > 0) (hy_pos : y > 0) (hlog_a_x : Real.logb a x = Real.logb a x) 
    (hlog_b_x : Real.logb b x = Real.logb b x) (hlog2_6 : Real.logb 2 6 = Real.logb 2 6) 
    (hlog3_6 : Real.logb 3 6 = Real.logb 3 6) (hlog2_3 : Real.logb 2 3 = Real.logb 2 3) 
    (hlog3_2 : Real.logb 3 2 = Real.logb 3 2) (hsum_nonneg : Real.logb 2 6 + Real.logb 3 6 ≥ 0) 
    (hlog2_3_nonneg : Real.logb 2 3 ≥ 0) (hlog3_2_nonneg : Real.logb 3 2 ≥ 0) : 
    Real.sqrt (Real.logb 2 6 + Real.logb 3 6) = Real.sqrt (Real.logb 2 3) + Real.sqrt (Real.logb 3 2) := sorry

theorem inequality_power_mean (a : ℝ) (b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) : ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := sorry

theorem find_expression_value (a b x y : ℝ) (h1 : a * x + b * y = 3) (h2 : a * x^2 + b * y^2 = 7) 
    (h3 : a * x^3 + b * y^3 = 16) (h4 : a * x^4 + b * y^4 = 42) : a * x^5 + b * y^5 = 20 := sorry

theorem periodic_function_exists (a : ℝ) (ha : a > 0) (f : ℝ → ℝ) 
    (hf1 : ∀ x : ℝ, f (x + a) = 1/2 + Real.sqrt (f x - (f x)^2)) 
    (hf2 : ∀ x : ℝ, f x - (f x)^2 ≥ 0) : 
    ∃ b : ℝ, b > 0 ∧ ∀ x : ℝ, f (x + b) = f x := sorry

theorem units_digit_eq_two : ((29 : ℤ) * 79 + (31 : ℤ) * 81) % 10 = 2 := sorry

theorem remainder_194_mod_11_eq_7 : (194 : ℤ) % (11 : ℤ) = (7 : ℤ) := sorry

theorem inequality_bounds (a b c : ℝ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : a + b + c = 2) (h4 : a * b + b * c + c * a = 1) : 
    0 ≤ a ∧ a ≤ 1/3 ∧ 1/3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ 4/3 := sorry

theorem integer_values_in_absolute_inequality : 
    let π : ℝ := 3.14159 in
    Finset.card (Finset.filter (λ (x : ℤ) => |(x : ℝ)| < 3 * π) Finset.univ) = 19 := sorry

theorem find_difference (x y : ℕ) (h_sum : x + y = 17402) (h_div : 10 ∣ x) (h_erase : y = x / 10) : x - y = 15762 := sorry

theorem sequence_sum_property (a b : ℕ → ℝ) (h : ∀ n, (a (n + 1), b (n + 1)) = (Real.sqrt 3 * a n - b n, Real.sqrt 3 * b n + a n)) (h100 : (a 100, b 100) = (2, 4)) : a 1 + b 1 = 1 / ((2 : ℝ) ^ 98) := sorry

theorem prime_sum_equation (m n : ℕ) (hm : Nat.Prime m) (hn : Nat.Prime n) (k t : ℕ) (hk : k > 0) (ht : t > 0) (hkt : k > t) (hquad : ∀ x : ℕ, x^2 - m * x + n = 0 ↔ x = k ∨ x = t) : m^n + n^m + k^t + t^k = 20 := sorry

theorem greater_even_integer : ∃ (n : ℕ), (2 * n) * (2 * n + 2) = 288 ∧ 2 * n + 2 = 18 := sorry

theorem sum_of_roots_eq_sqrt_five (a b : ℝ) (ha_pos : a > 0) (hb_pos : b > 0) (h_ne : a ≠ b) 
    (ha_eq : a - (1 / a) = 1) (hb_eq : b - (1 / b) = 1) : a + b = Real.sqrt 5 := sorry

theorem triangle_inequality_expression (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) 
    (h1 : a + b > c) (h2 : a + c > b) (h3 : b + c > a) : 
    a ^ 2 * (b + c - a) + b ^ 2 * (c + a - b) + c ^ 2 * (a + b - c) ≤ 3 * a * b * c := sorry

theorem find_B_value (z : ℂ) (A B C D : ℝ) (r₁ r₂ r₃ r₄ r₅ r₆ : ℕ) 
    (h1 : ∀ (z : ℂ), (z ^ 6 - 10 * z ^ 5 + A * z ^ 4 + B * z ^ 3 + C * z ^ 2 + D * z + 16) = 0 → ∃ (n : ℕ), z = (n : ℂ))
    (h2 : (z : ℂ) ^ 6 - 10 * (z : ℂ) ^ 5 + A * (z : ℂ) ^ 4 + B * (z : ℂ) ^ 3 + C * (z : ℂ) ^ 2 + D * (z : ℂ) + 16 = 
          ((z : ℂ) - (r₁ : ℂ)) * ((z : ℂ) - (r₂ : ℂ)) * ((z : ℂ) - (r₃ : ℂ)) * ((z : ℂ) - (r₄ : ℂ)) * ((z : ℂ) - (r₅ : ℂ)) * ((z : ℂ) - (r₆ : ℂ)))
    (h3 : (r₁ : ℝ) * (r₂ : ℝ) * (r₃ : ℝ) * (r₄ : ℝ) * (r₅ : ℝ) * (r₆ : ℝ) = (16 : ℝ))
    (h4 : (r₁ : ℝ) + (r₂ : ℝ) + (r₃ : ℝ) + (r₄ : ℝ) + (r₅ : ℝ) + (r₆ : ℝ) = (10 : ℝ)) : 
    B = -88 := sorry

theorem solve_for_a_plus_b (a b : ℝ) (h_b_ne_zero : b ≠ 0) (h1 : a ^ 2 * b ^ 3 = (32 : ℝ)/27) (h2 : a / b ^ 3 = (27 : ℝ)/4) : a + b = (8 : ℝ)/3 := sorry

theorem find_n_value (x : ℝ) (n : ℕ) (h1 : 2*x - 3 = a₁) (h2 : 5*x - 11 = a₂) (h3 : 3*x + 1 = a₃) 
    (h_arithmetic : a₂ - a₁ = a₃ - a₂) (h_nth_term : aₙ = 2009) : n = ?_ := sorry

