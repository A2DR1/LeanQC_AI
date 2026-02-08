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

theorem product_of_orders_not_power_of_two (G : Type*) [Group G] [Fintype G] [CommGroup G] : 
    let P := ∏ g : G, orderOf g in
    let n := 2009 in
    P ≠ 2 ^ n := sorry

theorem smallest_constant_integral_bound : 
    ∃! (C : ℝ), (∀ (P : ℝ → ℝ), (∃ (a b c d : ℝ), ∀ (x : ℝ), P x = a * x ^ 3 + b * x ^ 2 + c * x + d) → 
    (∃ (t : ℝ), t ∈ Set.Icc (0 : ℝ) 1 ∧ P t = 0) → 
    let M := sSup (Set.range (λ x : ℝ ↦ |P x|) ∩ {y | y ∈ Set.Icc (0 : ℝ) 1}) in 
    ∫ x in (0 : ℝ)..1, |P x| ≤ C * M) ∧ 
    C = 5/6 := sorry

theorem min_punches_to_clear_plane : 
    ∃ (punches : Finset (ℝ × ℝ)), Finset.card punches = 3 ∧ 
    (∀ (P : ℝ × ℝ), ∃ (C : ℝ × ℝ), C ∈ punches ∧ Irrational (Real.dist P C)) := sorry

theorem limit_of_density_zero (a : ℕ → ℕ) (ha : ∀ n, a n > 0) (S : ℝ) (hS : S = ∑' n, 1 / (a n : ℝ)) (hS_finite : Summable fun n => 1 / (a n : ℝ)) (b : ℕ → ℕ) (hb : ∀ n, b n = Finset.card (Finset.filter (fun k => a k ≤ n) Finset.univ)) : Filter.Tendsto (fun n : ℕ => (b n : ℝ) / (n : ℝ)) Filter.atTop (𝓝 0) := sorry

theorem determinant_of_matrix_with_generating_function_coefficients (n : ℕ) (hn : n > 0) :
    let c : ℕ → ℕ := fun k => 
      have h : ∃ (f : ℕ → ℕ), (fun (x : ℝ) => (1 - 3*x - Real.sqrt (1 - 14*x + 9*x^2)) / 4) = 
        Real.analyticAt 0 (fun x => ∑' k : ℕ, (f k : ℝ) * x ^ k) := by
        sorry
      Classical.choose h k
    let A : Matrix (Fin n) (Fin n) ℕ := 
      Matrix.of (fun i j : Fin n => c (i.val + j.val + 1))
    in (A.map (Nat.cast : ℕ → ℤ)).det = (10 : ℤ) ^ ((n : ℕ).choose 2) := sorry

theorem product_maximization : 
    let n := 660 in
    let a : ℕ → ℕ := a in
    (∀ a : ℕ → ℕ, (∑ i in Finset.Icc 1 n, a i) = 1979 → 
      (∃ (b : ℕ → ℕ), (∑ i in Finset.Icc 1 n, b i) = 1979 ∧ 
        (∀ i, b i = 3 ∨ b i = 2) ∧ 
        (∃! j, b j = 2) ∧ 
        (∏ i in Finset.Icc 1 n, a i) ≤ (∏ i in Finset.Icc 1 n, b i))) := sorry

theorem not_divisible_by_odd_prime (p : ℕ) (hp : Nat.Prime p) (hp_odd : Odd p) (F : ℤ → ℤ) (hF : ∀ n, F n = ∑ k in Finset.range (p - 1), (k + 1) * n ^ k) (a b : ℤ) (ha : a ∈ Finset.Icc (0 : ℤ) (p - 1)) (hb : b ∈ Finset.Icc (0 : ℤ) (p - 1)) (hne : a ≠ b) : ¬ p ∣ F a - F b := sorry

theorem determinant_of_pair_count_matrix (n : ℕ) (hn : n > 0) :
    let I : Finset ℕ := Finset.Icc 1 n
    let s (i j : ℕ) : ℕ := Finset.card ((Finset.filter (λ (p : ℕ × ℕ) => p.1 * i + p.2 * j = n) (Finset.Ico 0 (n + 1)).product (Finset.Ico 0 (n + 1))).filter (λ p => 0 ≤ p.1 ∧ 0 ≤ p.2))
    let S : Matrix (Fin n) (Fin n) ℕ := Matrix.of (λ i j => s ((i : ℕ) + 1) ((j : ℕ) + 1))
    in Matrix.det (S.map (Nat.cast : ℕ → ℤ)) = (-1 : ℤ) ^ ((n + 1) / 2 - 1) * 2 * ((n + 1) / 2 : ℤ) := sorry

theorem possible_cardinalities_of_self_cross_set (n : ℕ) (hn : n > 0) : 
    (∃ (S : Set (ℝ × ℝ × ℝ)) (hS_fin : Set.Finite S) (hS_card : Nat.card S = n), 
      (∀ v ∈ S, ∀ w ∈ S, (Prod.fst v * Prod.fst w, Prod.snd v * Prod.fst w, Prod.snd v * Prod.snd w) ∈ S) ∧ 
      (∀ x ∈ S, ∃ v w, v ∈ S ∧ w ∈ S ∧ x = (Prod.fst v * Prod.fst w, Prod.snd v * Prod.fst w, Prod.snd v * Prod.snd w))) → 
    n = 1 ∨ n = 7 := sorry

theorem not_divides_pow_two_sub_one : ∀ (n : ℤ), n > 1 → ¬ n ∣ (2 ^ n - 1) := sorry

theorem supremum_derivative_at_zero : sSup {|(P.derivative.eval 0)| | (P : ℝ[X]) (hP : P ∈ {P : ℝ[X] | P.degree ≤ 2 ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, |P.eval x| ≤ 1})} = 8 := sorry

theorem infinite_intersection_empty : ⋂ n : ℕ, (fun (x : {x : ℚ // x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1}) => (⟨x.val - 1 / x.val, by
    have hx := x.property
    rcases hx with ⟨hx1, hx2, hx3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro h
      have : x.val - 1 / x.val = -1 := h
      have h' : x.val - 1 / x.val = -1 := h
      have : 1 / x.val = x.val + 1 := by linarith
      have hdiv : 1 / x.val = x.val + 1 := by linarith
      have : x.val * (x.val + 1) = 1 := by
        field_simp [hx2]
        linarith
      have : x.val ^ 2 + x.val - 1 = 0 := by ring_nf at this; nlinarith
      have sol1 : ℚ := (-1 + Real.sqrt 5) / 2
      have sol2 : ℚ := (-1 - Real.sqrt 5) / 2
      sorry
    · intro h
      have : x.val - 1 / x.val = 0 := h
      have : 1 / x.val = x.val := by linarith
      have : x.val ^ 2 = 1 := by
        field_simp [hx2]
        linarith
      have : x.val = 1 ∨ x.val = -1 := by
        nlinarith
      cases' this with hpos hneg
      · exact hx3 hpos
      · exact hx1 hneg
    · intro h
      have : x.val - 1 / x.val = 1 := h
      have : 1 / x.val = x.val - 1 := by linarith
      have : x.val * (x.val - 1) = 1 := by
        field_simp [hx2]
        linarith
      have : x.val ^ 2 - x.val - 1 = 0 := by ring_nf at this; nlinarith
      have sol1 : ℚ := (1 + Real.sqrt 5) / 2
      have sol2 : ℚ := (1 - Real.sqrt 5) / 2
      sorry⟩) : {x : ℚ // x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1}) ^ n '' (Set.univ : Set {x : ℚ // x ≠ -1 ∧ x ≠ 0 ∧ x ≠ 1})) = ∅ := sorry

theorem binomial_sum_identity (n : ℕ) (hn : n > 0) : 
    let S := ∑ k in Finset.range n, ((2 : ℝ) ^ (n - k)) * (((-1 : ℝ)) ^ k) * ((Nat.choose n k) : ℝ) * ((2 : ℝ) - 1) ^ (-(n : ℤ)) in
    S = 1/2 := sorry

theorem limit_ratio_equals_e : 
    ∀ (x : ℝ) (hx : x > 0), 
    let g : ℝ → ℝ := λ x => 
      have h : Filter.Tendsto (λ (r : ℝ) => ((x + 1) ^ (r + 1) - x ^ (r + 1)) ^ (1 / r)) (𝓝 0) (𝓝 (g x)) := by
        exact ?_
      g x
    in Filter.Tendsto (λ (x : ℝ) => g x / x) Filter.atTop (𝓝 (Real.exp 1)) := sorry

theorem smallest_g : ∃! g : ℝ, 0 < g ∧ (∀ n : ℕ, n ≥ 1 → ∃ (c d : ℕ) (hc : c + d = n), r_n n = |(c : ℝ) - (d : ℝ) * Real.sqrt 3| ∧ |(c : ℝ) - (d : ℝ) * Real.sqrt 3| ≤ g) ∧ (∀ g' : ℝ, 0 < g' ∧ (∀ n : ℕ, n ≥ 1 → ∃ (c d : ℕ) (hc : c + d = n), r_n n = |(c : ℝ) - (d : ℝ) * Real.sqrt 3| ∧ |(c : ℝ) - (d : ℝ) * Real.sqrt 3| ≤ g') → g ≤ g') := sorry

theorem exists_circle_with_zero_integral (h : ℝ × ℝ → ℝ) (hdiff : ContDiff ℝ 2 h) (d r : ℝ) (hd_pos : d > 0) (hr_pos : r > 0) (hd_gt_r : d > r) :
    ∃ (center : ℝ × ℝ), ‖center‖ = d ∧
    let 𝒮 : Set (ℝ × ℝ) := {p | ‖p - center‖ = r} in
    ∫ x in {p | ‖p - center‖ ≤ r}, (snd x * (fderiv ℝ h x).1 (1,0) - fst x * (fderiv ℝ h x).1 (0,1)) = 0 := sorry

theorem integral_of_special_function : 
    let a := π / 2 in
    let f (x : ℝ) : ℝ := 1 / (1 + (Real.tan x) ^ (Real.sqrt 2)) in
    ∫ x in (0 : ℝ)..a, f x = π / 4 := sorry

theorem function_form : ∃ (a : ℝ) (c : ℝ), a > 0 ∧ ∀ (x : ℝ), 0 ≤ x → (c > 0 → x < 1 / c) → (∀ (f : ℝ → ℝ) (I : Set ℝ), I = Set.Icc (0 : ℝ) (1 / c) → (∀ x ∈ I, x > 0 → (∫ t in (0 : ℝ)..x, f t) / x = Real.sqrt (f 0 * f x)) → f x = a / ((1 - c * x) ^ 2)) ∧ (c ≤ 0 → ∀ (f : ℝ → ℝ) (I : Set ℝ), I = Set.Icc (0 : ℝ) ∞ → (∀ x ∈ I, x > 0 → (∫ t in (0 : ℝ)..x, f t) / x = Real.sqrt (f 0 * f x)) → f x = a / ((1 - c * x) ^ 2)) := sorry

theorem probability_of_property_P (k : ℕ) (hk : k > 0) : 
    let S := {σ : Equiv.Perm (Fin (3*k+1)) | True} in
    let P (σ : Equiv.Perm (Fin (3*k+1))) : Prop := 
      ∀ (i : ℕ) (hi : i ≤ 3*k+1), ¬3 ∣ (Finset.sum (Finset.range i) fun j => ((σ j : ℤ) : ℤ))) in
    (Nat.card {σ ∈ S | P σ}).toReal / (Nat.card S).toReal = 
      ((Nat.factorial k) * (Nat.factorial (k+1)) : ℕ).toReal / (((3*k+1) * (Nat.factorial (2*k)) : ℕ).toReal) := sorry

theorem exists_monochromatic_pair_with_distance : 
    ∃ (p q : ℝ × ℝ) (hp : p ∈ {x : ℝ × ℝ | x.1 ≥ 0 ∧ x.2 ≥ 0 ∧ x.1 + x.2 ≤ 1}) 
    (hq : q ∈ {x : ℝ × ℝ | x.1 ≥ 0 ∧ x.2 ≥ 0 ∧ x.1 + x.2 ≤ 1}) (color : Fin 4), 
    c p = color ∧ c q = color ∧ Real.dist p q ≥ 2 - Real.sqrt 2 := sorry

theorem infinite_triples_in_S : ∀ N : ℤ, ∃ n : ℤ, n ≥ N ∧ n ∈ {n : ℤ | ∃ a b : ℤ, n = a ^ 2 + b ^ 2} ∧ (n + 1) ∈ {n : ℤ | ∃ a b : ℤ, n = a ^ 2 + b ^ 2} ∧ (n + 2) ∈ {n : ℤ | ∃ a b : ℤ, n = a ^ 2 + b ^ 2} := sorry

theorem series_sum_eq : ∀ (x : ℝ) (h_x_range : x > 0 ∧ x < 1) (f : ℕ → ℝ) (h_f_def : ∀ n, f n = x ^ (2 ^ n) / (1 - x ^ (2 ^ (n + 1)))) (S : ℝ) (h_S_def : S = ∑' n, f n), S = x / (1 - x) := sorry

theorem max_negative_coefficients_of_square (n : ℤ) (hn : n ≥ 2) (p : Polynomial ℝ) (hp : Polynomial.natDegree p = n) :
    let S := p ^ 2
    let negative_coeffs := Finset.filter (fun (k : ℕ) => S.coeff k < 0) (Finset.range (2 * n + 1).toNat)
    Finset.card negative_coeffs ≤ 2 * n - 2 := sorry

theorem convergence_iff_balanced : (balanced → Summable (λ n : ℕ => a_n n * (n : ℝ))) ∧ (Summable (λ n : ℕ => a_n n * (n : ℝ)) → balanced) := sorry

theorem eq_of_mul_eq_mul (S : Type) [SetLike S] (mul : S → S → S) (h_comm : ∀ x y : S, mul x y = mul y x) (h_assoc : ∀ x y z : S, mul (mul x y) z = mul x (mul y z)) (h_div : ∀ x y : S, ∃ z : S, mul x z = y) (a b c : S) (h : mul a c = mul b c) : a = b := sorry

theorem count_inverse_decreasing (p : ℕ) (hp : Nat.Prime p) (hpgt : 3 < p) : 
    let K : Set ℕ := {k | 1 ≤ k ∧ k ≤ p - 1}
    let I : ℕ → ℕ := λ k => if h : k ∈ K then Nat.find (Nat.exists_mul_mod_eq_one_of_coprime (by
        have := Nat.prime.coprime_iff_not_dvd hp (by
          intro hdiv
          have := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (by omega) (Nat.succ_le_of_lt hpgt))
          have hk : k ≤ p - 1 := by
            simpa [K, Set.mem_setOf_eq] using h
          have : k < p := by omega
          exact Nat.le_of_dvd (by omega) (hp.dvd_mul.mp hdiv |>.resolve_right ?_) at this
          omega) ?_)
        exact ?_) else 1
    in
    let S : Finset ℕ := Finset.filter (λ k => I (k + 1) < I k) (Finset.Icc 1 (p - 2))
    in p/4 - 1 < S.card := sorry

theorem integral_inequality (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1)) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, |f x + f y| ∂y ∂x ≥ ∫ x in (0 : ℝ)..1, |f x| ∂x := sorry

theorem product_sin_ratio_bound (n : ℕ) (a : ℕ → ℝ) (hpos : ∀ i, 0 < a i ∧ a i < π) (μ : ℝ) (h_μ : μ = (∑ i in Finset.range n, a i) / (n : ℝ)) : 
    ∏ i in Finset.range n, (Real.sin (a i) / a i) ≤ ((Real.sin μ) / μ) ^ n := sorry

theorem unique_f_on_interval : ∃! (f : Set.Icc (-1 : ℝ) 1 → ℝ),
  ContinuousOn f (Set.Icc (-1 : ℝ) 1) ∧
  f ⟨0, by constructor <;> norm_num⟩ = 1 ∧
  (∀ x : Set.Icc (-1 : ℝ) 1, f x = ((2 - (x : ℝ)^2) / 2) * f ⟨(x : ℝ)^2 / (2 - (x : ℝ)^2), by
    have hx : (x : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := x.2
    rcases hx with ⟨hleft, hright⟩
    constructor
    · nlinarith [sq_nonneg (x : ℝ)]
    · nlinarith⟩) ∧
  (∃ L : ℝ, Tendsto (λ x : ℝ ↦ f ⟨x, by exact And.intro (by linarith [show x ≤ 1 from ?_]) (by linarith)⟩ / Real.sqrt (1 - x)) (𝓝[<] (1 : ℝ)) (𝓝 L)) ∧
  ∀ x : Set.Icc (-1 : ℝ) 1, f x = Real.sqrt (1 - (x : ℝ)^2) := sorry

theorem sum_formula (k : ℕ) : ∑ j in Finset.range (k + 1), (2 : ℕ) ^ (k - j) * Nat.choose (k + j) j = (4 : ℕ) ^ k := sorry

theorem max_cyclic_pair_sum (n : ℕ) (hn : n ≥ 2) : 
    ∃ (perm : Equiv.Perm (Fin n)), 
      ∀ (σ : Equiv.Perm (Fin n)), 
        let x : Fin n → ℕ := λ i => (σ i).val + 1
        in ∑ i : Fin n, (x i) * (x ((i + 1) % n)) ≤ 
           ∑ i : Fin n, ((perm i).val + 1) * ((perm ((i + 1) % n)).val + 1) ∧
           ∑ i : Fin n, ((perm i).val + 1) * ((perm ((i + 1) % n)).val + 1) = 
           (2 * n ^ 3 + 3 * n ^ 2 - 11 * n + 18) / 6 := sorry

theorem polynomial_max_coefficient_condition (p : ℝ → ℝ) (h_deg : Polynomial.degree (Polynomial.ofFinsupp (Polynomial.toFinsupp p)) = 4) (h_range : ∀ x, -1 ≤ x ∧ x ≤ 1 → 0 ≤ p x ∧ p x ≤ 1) (h_max_coeff : ∀ (q : ℝ → ℝ), (Polynomial.degree (Polynomial.ofFinsupp (Polynomial.toFinsupp q)) = 4) → (∀ x, -1 ≤ x ∧ x ≤ 1 → 0 ≤ q x ∧ q x ≤ 1) → Polynomial.coeff (Polynomial.ofFinsupp (Polynomial.toFinsupp q)) 4 ≤ Polynomial.coeff (Polynomial.ofFinsupp (Polynomial.toFinsupp p)) 4) : p = (λ x => 4*x^4 - 4*x^2 + 1) := sorry

theorem solution_of_differential_equation (n : ℕ) (f : ℝ → ℝ) (hf : ∀ x, 1 ≤ x → ContinuousAt f x) :
    ∃ (y z : ℝ → ℝ), (∀ x, 1 ≤ x → (∏ k in Finset.range n, (x * deriv (fun t => deriv (fun s => y s) t) x - (k : ℝ))) y x = f x) ∧
    (∀ k : ℕ, k < n → deriv^[k] y 1 = 0) ∧ (∀ x, y x = ∫ t in (1 : ℝ)..x, z t) ∧
    (∀ x, y x = ∫ t in (1 : ℝ)..x, ((x - t) ^ (n - 1) * f t) / ((Nat.factorial (n - 1)) * t ^ n)) := sorry

theorem infinite_sum_odd_divisors_eq_pi_sq_div_sixteen : 
    HasSum (λ (k : ℕ) => (-1 : ℝ) ^ (k - 1) * (Real.ofNat (A k) / (k : ℝ))) ((π : ℝ) ^ 2 / 16) := sorry

theorem prime_representations_equivalence :
    {p : ℕ | Nat.Prime p ∧ p > 2 ∧ (∃ (x y : ℤ), p = x^2 + 16 * y^2)} = {p : ℕ | Nat.Prime p ∧ p > 2 ∧ p % 8 = 1} ∧
    {p : ℕ | Nat.Prime p ∧ p > 2 ∧ (∃ (x y : ℤ), p = 4*x^2 + 4*x*y + 5*y^2)} = {p : ℕ | Nat.Prime p ∧ p > 2 ∧ p % 8 = 5} := sorry

theorem count_non_spiral_points : Finset.card (S \ T) = 10053 := sorry

theorem max_rational_points_on_circle_with_irrational_center : 
    ∀ (a b : ℝ) (h_center : ¬(a ∈ Set.range (algebraMap ℚ ℝ) ∧ b ∈ Set.range (algebraMap ℚ ℝ))) (r : ℝ) (hr : r > 0), 
    let S : Set (ℝ × ℝ) := {P | P.1 ∈ Set.range (algebraMap ℚ ℝ) ∧ P.2 ∈ Set.range (algebraMap ℚ ℝ) ∧ (P.1 - a)^2 + (P.2 - b)^2 = r^2} in
    Finset.card (S.toFinite.toFinset) ≤ 2 := sorry

theorem injective_f : Function.Injective (f : S → ℤ) := sorry

theorem exists_closed_hemisphere_with_four_points (S : Set (ℝ × ℝ × ℝ)) (hS : S = Metric.sphere (0 : ℝ × ℝ × ℝ) 1) (P : Set (ℝ × ℝ × ℝ)) (hP : P ⊆ S) (hP_card : Finset.card (Finset.filter (fun p => p ∈ P) (Finset.filter (fun p => p ∈ S) Finset.univ).toFinset) = 5) : ∃ (H : Set (ℝ × ℝ × ℝ)), (∃ (v : ℝ × ℝ × ℝ), ‖v‖ = 1 ∧ H = {x : ℝ × ℝ × ℝ | x ∈ S ∧ inner (x.1, x.2.1, x.2.2) (v.1, v.2.1, v.2.2) ≥ 0}) ∧ ∃ (Q : Set (ℝ × ℝ × ℝ)), Q ⊆ P ∧ Set.ncard Q = 4 ∧ Q ⊆ H := sorry

theorem exists_expression_for_every_element (G : Type*) [Group G] [Fintype G] (g h : G) (h_gen : Subgroup.closure {g, h} = ⊤) (h_order : ∃ (k : ℕ), orderOf g = 2 * k + 1) : 
    ∀ x : G, ∃ (r : ℕ) (hr : 1 ≤ r ∧ r ≤ Fintype.card G) (m n : Fin r → ℤ) (hm : ∀ i, m i = -1 ∨ m i = 1) (hn : ∀ i, n i = -1 ∨ n i = 1), 
    x = Finset.prod (Finset.univ : Finset (Fin r)) (λ i => g ^ (m i) * h ^ (n i)) := sorry

theorem limit_integral_expression (I : ℝ → ℝ) (hI : ∀ (R : ℝ), I R = ∫ x in Set.Icc (-R) R, ∫ y in Set.Icc (-Real.sqrt (R^2 - x^2)) (Real.sqrt (R^2 - x^2)), ((1 + 2*x^2) / (1 + x^4 + 6*x^2*y^2 + y^4) - (1 + y^2) / (2 + x^4 + y^4))) :=
  Filter.Tendsto I Filter.atTop (𝓝 ((Real.sqrt 2 / 2) * π * Real.log 2)) := sorry

theorem integral_inequality (f : ℝ × ℝ → ℝ) (hf : ContinuousOn f (Set.prod (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1))) :
    (∫ y in (0 : ℝ)..1, (∫ x in (0 : ℝ)..1, f (x, y)) ^ 2) + (∫ x in (0 : ℝ)..1, (∫ y in (0 : ℝ)..1, f (x, y)) ^ 2) ≤
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f (x, y)) ^ 2 + (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, (f (x, y)) ^ 2) := sorry

theorem count_functions_with_iterate_bounded (n : ℕ) (k : ℕ) (hk : k ≤ n) :
    let X := Finset.Icc 1 n in
    let valid_functions := {f : ℕ → ℕ | ∀ x ∈ X, ∃ (j : ℕ), (Nat.iterate f j x) ≤ k} in
    Finset.card (Finset.filter (λ f => ∀ x ∈ X, ∃ (j : ℕ), (Nat.iterate f j x) ≤ k) (Finset.pi X (λ _ => X))) = k * n ^ (n - 1) := sorry

theorem find_example : ∃ (α : Type) (S : Set α) (op : α → α → α), (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, op (op a b) (op c d) = op a d) ∧ (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, (op a b = c → op c c = c)) ∧ (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, (op a b = c → op a d = op c d)) ∧ (∀ a ∈ S, op a a = a) ∧ (∃ a ∈ S, ∃ b ∈ S, op a b = a ∧ a ≠ b) ∧ (∃ a ∈ S, ∃ b ∈ S, op a b ≠ a) := sorry

theorem limit_sum_product_eq_three : 
    Filter.Tendsto (λ (p : ℝ × ℝ) ↦ ((1 - p.1 * (p.2)^2) * (1 - (p.1)^2 * p.2) * 
      ∑' (m : ℕ) (n : ℕ), if m > 0 ∧ n > 0 ∧ (1/2 : ℝ) ≤ (m : ℝ)/n ∧ (m : ℝ)/n ≤ 2 then (p.1)^m * (p.2)^n else 0))
    (nhdsWithin ((1 : ℝ), (1 : ℝ)) {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 < 1 ∧ z.2 < 1}) 
    (nhds (3 : ℝ)) := sorry

theorem inequality_condition (x y : ℝ) (hy_nonneg : y ≥ 0) (h_ineq : y * (y + 1) ≤ (x + 1)^2) : y * (y - 1) ≤ x^2 := sorry

theorem limit_behavior_of_g (r : ℝ) (hr : r > 1) (g : ℝ → ℝ) (hcont : ContinuousOn g (Set.Icc (0 : ℝ) 1)) (hdiff : ∀ x ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ g x) (hdiff2 : ∀ x ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ (deriv g) x) (hlimit : Filter.Tendsto (λ x : ℝ => g x / x ^ r) (𝓝[>] 0) (𝓝 0)) : 
    (Filter.Tendsto (deriv g) (𝓝[>] 0) (𝓝 0)) ∨ (Filter.limsup (λ x : ℝ => x ^ r * |deriv (deriv g) x|) (𝓝[>] 0) = ∞) := sorry

theorem power_series_zero_coefficients (a b : ℝ) (ha : a > 0) (hb : b > 0) : 
    let f : ℝ → ℝ := fun x => Real.exp (a * x) * Real.cos (b * x) in
    let S := HasFPowerSeriesOnBall f (Real.analyticAt_exp (a * 0)).powerSeries (Real.analyticAt_exp (a * 0)).center (Real.analyticAt_exp (a * 0)).radius in
    (∀ n, S.powerSeries.coeff n = 0) ∨ (Set.Infinite {n | S.powerSeries.coeff n ≠ 0}) := sorry

theorem sum_alternating_binary_digits_power (m : ℕ) (hm : m > 0) : 
    ∑ k in Finset.range (2^m), (-1 : ℤ) ^ (Nat.bits (k : ℕ)) * (k : ℤ) ^ m = 
    (-1 : ℤ) ^ m * (2 : ℤ) ^ ((m * (m - 1)) / 2) * (Nat.factorial m : ℤ) := sorry

theorem pi_times_T1_squared_eq_two : π * (T 1) ^ 2 = 2 := sorry

theorem dense_set_of_powers_of_two_and_three : Dense (Subtype.val ⁻¹' (S : Set ℝ) : Set {x : ℝ // x > 0}) := sorry

theorem function_behavior (c : ℝ) (hc : c > 0) (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_eq : ∀ x : ℝ, f x = f (x ^ 2 + c)) :
  (c ≤ 1/4 → ∀ x y : ℝ, f x = f y) ∧
  (c > 1/4 → ∀ (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) c)) (hg_end : g 0 = g c),
    ∃ (f : ℝ → ℝ), Continuous f ∧ (∀ x, f x = f (x ^ 2 + c)) ∧ (∀ x ∈ Set.Icc (0 : ℝ) c, f x = g x) ∧ (∀ x < 0, f x = f (-x))) := sorry

theorem exists_N_with_many_palindromic_bases : ∃ (N : ℕ), ∃ (S : Finset ℕ), S.card ≥ 2002 ∧ (∀ b ∈ S, b > 2) ∧ (∀ b ∈ S, let digits := Nat.digits b N in digits.length = 3 ∧ digits.reverse = digits) := sorry

theorem unique_solution : ∃! (x : ℝ) (y : ℝ), (1 / x + 1 / (2 * y) = (x ^ 2 + 3 * y ^ 2) * (3 * x ^ 2 + y ^ 2)) ∧ (1 / x - 1 / (2 * y) = 2 * (y ^ 4 - x ^ 4)) ∧ (x = (Real.sqrt 5 ^ 3 + 1) / 2) ∧ (y = (Real.sqrt 5 ^ 3 - 1) / 2) := sorry

theorem zeros_of_g_prime_have_abs_one (n : ℕ) (p : ℂ → ℂ) (h_p_deg : Polynomial.degree (Polynomial.ofFunction p) = n) (h_p_zeros : ∀ z, p z = 0 → Complex.abs z = 1) (g : ℂ → ℂ) (h_g_def : ∀ z, g z = p z / z ^ (n / 2)) : ∀ z, Complex.deriv g z = 0 → Complex.abs z = 1 := sorry

theorem tan_sum_product_ratio_int (n : ℕ) (hn_pos : n > 0) (hn_odd : Odd n) (θ : ℝ) (h_irrational : Irrational (θ / π)) : 
    ∃ (m : ℤ), (∑ k in Finset.range n, Real.tan (θ + (k : ℝ) * π / (n : ℝ))) / (∏ k in Finset.range n, Real.tan (θ + (k : ℝ) * π / (n : ℝ))) = (m : ℝ) ∧ 
    ((n % 4 = 1 → m = (n : ℤ)) ∧ (n % 4 = 3 → m = -((n : ℤ)))) := sorry

theorem root_multiplicity_one_of_condition : 
    ∀ (r : ℝ), P r = 0 → Polynomial.rootMultiplicity r (Polynomial.ofFinsupp (Polynomial.toFinsupp P)) = 1 := sorry

theorem limit_of_sequence : Filter.Tendsto (fun (n : ℕ) => (∑ k in Finset.Ico 1 n, Real.sin (((2 : ℕ) * k - 1) * π / ((2 : ℕ) * n)) / ((Real.cos (((k - 1) * π) / ((2 : ℕ) * n))) ^ 2 * (Real.cos ((k * π) / ((2 : ℕ) * n))) ^ 2)) / (n ^ 3)) Filter.atTop (𝓝 ((8 : ℝ) / π ^ 3)) := sorry

theorem limit_k_over_x_zero : Filter.Tendsto (λ (x : ℝ) => (k x : ℝ) / x) Filter.atTop (𝓝 0) := sorry

theorem largest_constant_M (n : ℕ) (hn : n = 2019) (b : ℕ → ℝ) (h_b_nonzero : b n ≠ 0) (h_b_monotone : ∀ k, 0 ≤ k → k < n → b k < b (k + 1)) (h_b_bounds : ∀ k, k ≤ n → 1 ≤ b k ∧ b k ≤ n) : 
    ∃ M : ℝ, (∀ (b' : ℕ → ℝ) (h_b'_nonzero : b' n ≠ 0) (h_b'_monotone : ∀ k, 0 ≤ k → k < n → b' k < b' (k + 1)) (h_b'_bounds : ∀ k, k ≤ n → 1 ≤ b' k ∧ b' k ≤ n), 
    let P := fun (z : ℂ) => ∑ k in Finset.range (n + 1), (b' k : ℂ) * z ^ k in
    let roots := Complex.roots P in
    let μ := (∑ z in roots, Complex.abs z) / (n : ℝ) in
    μ ≥ M) ∧ 
    (∀ M' : ℝ, (∀ (b' : ℕ → ℝ) (h_b'_nonzero : b' n ≠ 0) (h_b'_monotone : ∀ k, 0 ≤ k → k < n → b' k < b' (k + 1)) (h_b'_bounds : ∀ k, k ≤ n → 1 ≤ b' k ∧ b' k ≤ n), 
    let P := fun (z : ℂ) => ∑ k in Finset.range (n + 1), (b' k : ℂ) * z ^ k in
    let roots := Complex.roots P in
    let μ := (∑ z in roots, Complex.abs z) / (n : ℝ) in
    μ ≥ M') → M' ≤ M) ∧ 
    M = (n : ℝ) ^ (-1 / (n : ℝ)) := sorry

theorem differential_system_control (T : ℝ) (hT_pos : T > 0) (x y u : ℝ → ℝ) (hu_cont : Continuous u) : 
    (∀ t, deriv x t = -2 * y t + u t ∧ deriv y t = -2 * x t + u t) → 
    ((x 0 ≠ y 0) → (∀ t, (x t, y t) ≠ (0, 0))) ∧ 
    ((x 0 = y 0) → (∃ u : ℝ → ℝ, Continuous u ∧ (∀ t, deriv x t = -2 * y t + u t ∧ deriv y t = -2 * x t + u t) ∧ (x T, y T) = (0, 0))) := sorry

theorem dance_relation_exists : ∃ (g h : G) (b c : B), D b g ∧ D c h ∧ ¬ D b h ∧ ¬ D c g := sorry

theorem alternating_sequences_maximize_f (n : ℤ) (hn : n ≥ 2) (s : Fin (n - 1) → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    let f : (Fin (n - 1) → ℤ) → ℕ := λ s => Finset.card (Finset.filter (λ (perm : Equiv.Perm (Fin n)) => 
      ∀ i : Fin (n - 1), s i * ((perm (Fin.succ i)) - perm i) > 0) Finset.univ)
    in ∀ (s' : Fin (n - 1) → ℤ), (∀ i, s' i = 1 ∨ s' i = -1) → f s' ≤ f s ↔ 
      (∀ i, s' i = (-1 : ℤ) ^ (i : ℤ + 1)) ∨ (∀ i, s' i = (-1 : ℤ) ^ (i : ℤ)) := sorry

theorem possible_values_of_T (A : ℝ) (hA : A > 0) (x : ℕ → ℝ) (hx_pos : ∀ j, x j > 0) (hS : HasSum x A) : 
    Set.range (fun (x : ℕ → ℝ) (hx_pos : ∀ j, x j > 0) (hS : HasSum x A) => HasSum (fun j => (x j) ^ 2) ?_) = Set.Ioo (0 : ℝ) (A ^ 2) := sorry

theorem square_vertices_from_inequality : ∀ (A B C : ℤ × ℤ), A ≠ B → B ≠ C → A ≠ C → 
  let dist (P Q : ℤ × ℤ) := Real.sqrt (((Q.1 : ℝ) - P.1) ^ 2 + ((Q.2 : ℝ) - P.2) ^ 2) in
  let area (P Q R : ℤ × ℤ) := |((Q.1 : ℝ) - P.1) * ((R.2 : ℝ) - P.2) - ((R.1 : ℝ) - P.1) * ((Q.2 : ℝ) - P.2)| / 2 in
  (dist A B + dist B C) ^ 2 < 8 * area A B C + 1 → 
  ∃ (S : ℤ × ℤ), ({A, B, C, S} : Set (ℤ × ℤ)).card = 4 ∧ 
    dist A B = dist B C ∧ dist B C = dist C S ∧ dist C S = dist S A ∧ dist A B = dist S A ∧
    dist A C = dist B S ∧ dist A B ^ 2 + dist B C ^ 2 = dist A C ^ 2 ∧ dist B C ^ 2 + dist C S ^ 2 = dist B S ^ 2 ∧
    dist C S ^ 2 + dist S A ^ 2 = dist C A ^ 2 ∧ dist S A ^ 2 + dist A B ^ 2 = dist S B ^ 2 := sorry

theorem polynomial_representation (n : ℕ) (hn : n > 0) : 
    (∃ (f : Polynomial ℤ) (h : f ∈ Subalgebra.range (MvPolynomial.aeval (fun (σ : Fin 2) => match σ with | 0 => MvPolynomial.X 0 | 1 => MvPolynomial.X 1) : ℤ → MvPolynomial (Fin 2) ℤ) 
      (MvPolynomial.map (Int.castRingHom ℤ) (P (MvPolynomial.X 0) (MvPolynomial.X 1)) ∧ MvPolynomial.map (Int.castRingHom ℤ) (Q (MvPolynomial.X 0) (MvPolynomial.X 1))))) 
      (∀ (x y : ℤ), eval₂ (Int.castRingHom ℤ) (fun i => match i with | 0 => x | 1 => y) f = F_n n x y)) ∨
    (∃ (g : Polynomial ℤ) (h : g ∈ Subalgebra.range (MvPolynomial.aeval (fun (σ : Fin 2) => match σ with | 0 => MvPolynomial.X 0 | 1 => MvPolynomial.X 1) : ℤ → MvPolynomial (Fin 2) ℤ) 
      (MvPolynomial.map (Int.castRingHom ℤ) (P (MvPolynomial.X 0) (MvPolynomial.X 1)) ∧ MvPolynomial.map (Int.castRingHom ℤ) (Q (MvPolynomial.X 0) (MvPolynomial.X 1))))) 
      (∀ (x y : ℤ), eval₂ (Int.castRingHom ℤ) (fun i => match i with | 0 => x | 1 => y) g = G_n n x y)) := sorry

theorem set_of_n_with_properties_eq_specific_set : {n : ℕ | n > 0 ∧ n < 10^100 ∧ n ∣ 2^n ∧ (n - 1) ∣ (2^n - 1) ∧ (n - 2) ∣ (2^n - 2)} = {2^2, 2^4, 2^8, 2^16} := sorry

theorem convex_region_bounded (S : Set (ℝ × ℝ)) (hS_convex : Convex ℝ S) (h_origin_in_S : (0, 0) ∈ S) 
    (h_ray_condition : ∀ (θ : ℝ), ∃ (r : ℝ), r > 0 ∧ (r * Real.cos θ, r * Real.sin θ) ∉ S) 
    (h_origin_or_closed : IsOpen S ∨ IsClosed S) : Bounded S := sorry

theorem polynomial_zero_if_laplacian_zero_and_sum_squares_divides (n : ℕ) (hn : n > 0) (P : MvPolynomial (Fin n) ℝ) :
    (∑ i : Fin n, MvPolynomial.deriv (MvPolynomial.deriv P i) i) = 0 ∧
    (∃ Q : MvPolynomial (Fin n) ℝ, P = (∑ i : Fin n, MvPolynomial.X i ^ 2) * Q) → P = 0 := sorry

theorem area_of_convex_set_containing_hyperbola_points : 
    ∀ (S : Set (ℝ × ℝ)), 
    Convex ℝ S ∧ 
    (∃ p, p ∈ S ∧ p ∈ {z : ℝ × ℝ | z.1 * z.2 = 1}) ∧ 
    (∃ q, q ∈ S ∧ q ∈ {z : ℝ × ℝ | z.1 * z.2 = -1}) → 
    let area := MeasureTheory.volume S in
    area ≥ 4 ∧ 
    (∃ (S_min : Set (ℝ × ℝ)), 
        Convex ℝ S_min ∧ 
        (∃ p, p ∈ S_min ∧ p ∈ {z : ℝ × ℝ | z.1 * z.2 = 1}) ∧ 
        (∃ q, q ∈ S_min ∧ q ∈ {z : ℝ × ℝ | z.1 * z.2 = -1}) ∧ 
        MeasureTheory.volume S_min = 4 ∧ 
        ∀ (T : Set (ℝ × ℝ)), 
            Convex ℝ T ∧ 
            (∃ p, p ∈ T ∧ p ∈ {z : ℝ × ℝ | z.1 * z.2 = 1}) ∧ 
            (∃ q, q ∈ T ∧ q ∈ {z : ℝ × ℝ | z.1 * z.2 = -1}) → 
            MeasureTheory.volume T ≥ 4) := sorry

theorem exists_matrix_with_conditions_iff_n_odd : 
    ∀ (n : ℕ) (hn : n > 0), 
      (∃ (M : Matrix (Fin n) (Fin n) ℤ), 
        (∀ i, (∑ j, M i j * M i j) % 2 = 0) ∧ 
        (∀ i j, i ≠ j → (∑ k, M i k * M j k) % 2 = 1)) ↔ 
      Odd n := sorry

theorem rational_exp_of_sum_binary_ones : ∃ (q : ℚ), (Real.exp (∑' (n : ℕ), (Nat.bitCount (Nat.ofDigits 2 (Nat.digits 2 n))) / ((n : ℝ) * ((n : ℝ) + 1)))) = (q : ℝ)) := sorry

theorem rationals_in_S : ∀ (q : ℚ), 0 < q → q ∈ {x | ∃ (n : ℕ) (hn : n ≥ 1), (a (n - 1) : ℚ) / (a n : ℚ) = x} := sorry

theorem average_local_maxima : 
    let S : Finset ℕ := Finset.Icc 1 n in
    let permutations : Finset (ℕ → ℕ) := 
      {π | π ∈ S.bijOn S ∧ ∀ x, x ∈ S → π x ∈ S} in
    let is_local_max (π : ℕ → ℕ) (k : ℕ) : Prop :=
      (k = 1 ∧ π 1 > π 2) ∨
      (1 < k ∧ k < n ∧ π (k - 1) < π k ∧ π k > π (k + 1)) ∨
      (k = n ∧ π (n - 1) < π n) in
    let total_maxima : ℕ := 
      Finset.sum permutations (fun π => 
        Finset.card (Finset.filter (fun k => is_local_max π k) S)) in
    n > 1 → 
      (total_maxima : ℝ) / (Finset.card permutations : ℝ) = ((n + 1) : ℝ) / 3 := sorry

theorem recurrence_sequence_identity : 
    let T : ℕ → ℕ := fun n => 
      match n with
      | 0 => 2
      | 1 => 3
      | 2 => 6
      | n + 3 => (n + 7) * T (n + 2) - 4 * (n + 3) * T (n + 1) + (4 * (n + 3) - 8) * T n
      end
    in ∀ n, T n = Nat.factorial n + 2 ^ n := sorry

theorem inequality_condition (n : ℕ) (hn : n > 1) (a : ℕ → ℝ) (A : ℝ) 
    (h_ineq : A + (∑ i in Finset.Icc 1 n, (a i) ^ 2) < (1 / ((n : ℝ) - 1)) * ((∑ i in Finset.Icc 1 n, a i) ^ 2)) :
    ∀ (i j : ℕ), 1 ≤ i → i < j → j ≤ n → A < 2 * (a i) * (a j) := sorry

theorem alternating_binary_primes_unique : ∃! (p : ℕ), Nat.Prime p ∧ (p.digits 10).Alternating (λ d => d = 1) (λ d => d = 0) ∧ (p.digits 10).head? = some 1 ∧ (p.digits 10).getLast? = some 1 := sorry

theorem polynomial_identity (m : ℤ) (hm_odd : Odd m) (hm_gt_one : 1 < m) : 
    let n := 2 * m
    let θ : ℂ := Complex.exp (2 * π * Complex.I / (n : ℂ))
    in (1 - θ)⁻¹ = ∑ k in Finset.range (m - 1), θ ^ (2 * k + 1) := sorry

theorem centroid_inequality (f : ℝ → ℝ) (hf_strictMono : StrictMonoOn f (Set.Icc (0 : ℝ) 1)) (hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1)) (hf_nonneg : ∀ x, 0 ≤ f x) :
    let R_area := ∫ x in (0 : ℝ)..1, f x
    let R_moment := ∫ x in (0 : ℝ)..1, x * f x
    let x₁ := R_moment / R_area
    let solid_volume := π * ∫ x in (0 : ℝ)..1, (f x) ^ 2
    let solid_moment := π * ∫ x in (0 : ℝ)..1, x * (f x) ^ 2
    let x₂ := solid_moment / solid_volume
    in x₁ < x₂ := sorry

theorem units_digit_of_N_eq_3 : (Nat.floor ((10 : ℝ) ^ (20000 : ℝ) / ((10 : ℝ) ^ (100 : ℝ) + (3 : ℝ)))) % 10 = 3 := sorry

theorem binomial_mod_prime (p : ℕ) (hp : Nat.Prime p) (m n : ℕ) (hmn : m ≥ n) : (Nat.choose (p * m) (p * n) : ℤ) ≡ (Nat.choose m n : ℤ) [ZMOD p] := sorry

theorem complex_modulus_one (z : ℂ) (h : 11 * z ^ 10 + 10 * I * z ^ 9 + 10 * I * z - 11 = 0) : Complex.abs z = 1 := sorry

theorem determinant_mod_p_relation (p : ℕ) (hp : Nat.Prime p) (x y z : ℤ) : 
    ∃ (a b c : ℤ) (poly : ℤ[X]), 
      Matrix.det (Matrix.of ![![x, y, z], ![x ^ p, y ^ p, z ^ p], ![x ^ (p ^ 2), y ^ (p ^ 2), z ^ (p ^ 2)]]) ≡ 
      poly.eval (a * x + b * y + c * z) [ZMOD p] := sorry

theorem sum_coefficient_bound (a : ℕ → ℕ → ℤ) (ha : ∀ (m n : ℕ), a m n = ((Polynomial.coeff ℤ) ((1 + Polynomial.X + Polynomial.X ^ 2) ^ m) n)) : 
    ∀ (k : ℕ), 0 ≤ ∑ i in Finset.range ((2 * k) / 3 + 1), (-1 : ℤ) ^ i * a (k - i) i ∧ ∑ i in Finset.range ((2 * k) / 3 + 1), (-1 : ℤ) ^ i * a (k - i) i ≤ 1 := sorry

theorem existence_of_individual_weights (n : ℕ) (hn : n > 0) (P : Set (Finset ℕ)) (hP_nonempty : P.Nonempty) (hP_subset : ∀ S ∈ P, S ⊆ Finset.Icc 1 n) (hP_union : ∀ S ∈ P, ∀ S' ∈ P, S ∪ S' ∈ P) (hP_inter : ∀ S ∈ P, ∀ S' ∈ P, S ∩ S' ∈ P) (hP_decrement : ∀ S ∈ P, S.Nonempty → ∃ T ∈ P, T ⊆ S ∧ T.card = S.card - 1) (f : Finset ℕ → ℝ) (hf_empty : f ∅ = 0) (hf_additive : ∀ S ∈ P, ∀ S' ∈ P, f (S ∪ S') = f S + f S' - f (S ∩ S')) : 
    ∃ (f_vals : ℕ → ℝ), ∀ S ∈ P, f S = ∑ i in S, f_vals i := sorry

theorem f_1987_eq_1984 : f 1987 = 1984 := sorry

theorem max_cardinality_T : Finset.card (Finset.image (λ (x : I → ℝ) => (sign (x 1), sign (x 2), sign (x 3), sign (x 4))) (Finset.filter (λ x => (∑ i : I, a i * x i = 0) ∧ (∑ i : I, b i * x i = 0) ∧ (∀ i : I, x i ≠ 0)) (Finset.pi Finset.univ (λ _ => Finset.univ : Finset ℝ)))) ≤ 8 := sorry

theorem composite_representation (n : ℕ) (hn : n ≥ 1) (hcomp : ∃ (a b : ℕ), a ≥ 1 ∧ b ≥ 1 ∧ n = a * b) : ∃ (x y z : ℕ), x ≥ 1 ∧ y ≥ 1 ∧ z ≥ 1 ∧ n = x * y + x * z + y * z + 1 := sorry

theorem inequality_for_n_gt_one : ∀ (n : ℤ), n > 1 → (1 / (2 * n * Real.e) : ℝ) < ((1 / Real.e) - ((1 : ℝ) - (1 / (n : ℝ))) ^ (n : ℕ)) ∧ ((1 / Real.e) - ((1 : ℝ) - (1 / (n : ℝ))) ^ (n : ℕ)) < (1 / (n * Real.e) : ℝ) := sorry

theorem exists_function_g : ∃ (g : ℝ → ℝ), ∀ (x y : ℝ), f (x, y) = g x - g y := sorry

theorem disjoint_cover_contradiction : ¬∃ (α β γ : ℝ) (hα : α > 0) (hβ : β > 0) (hγ : γ > 0),
    let S (x : ℝ) : Set ℕ := {k | ∃ n : ℕ, k = ⌊n * x⌋.toNat} in
    Pairwise (Disjoint on S) [α, β, γ] ∧ ⋃ x ∈ ({α, β, γ} : Set ℝ), S x = Set.univ := sorry

theorem polynomial_divisibility_condition (f : ℤ[X]) (hf : f ≠ C (f.coeff 0)) (hcoeff : ∀ i, f.coeff i ≥ 0) (hn : n > 0) :
    (f.eval (n : ℤ)) ∣ (f.eval ((f.eval (n : ℤ)) + 1)) ↔ n = 1 := sorry

theorem m_value_independent : ∀ (f : ℝ → ℝ → ℝ) (hf : f ∈ {f : ℝ → ℝ → ℝ | ∀ x ≥ (1 : ℝ), ∀ y ≥ (1 : ℝ), ContDiff ℝ 2 (fun (p : ℝ × ℝ) => f p.1 p.2) ∧
    (∀ x ≥ (1 : ℝ), ∀ y ≥ (1 : ℝ), x * fderiv ℝ (fun (x' : ℝ) => f x' y) x + y * fderiv ℝ (fun (y' : ℝ) => f x y') y = x * y * Real.log (x * y)) ∧
    (∀ x ≥ (1 : ℝ), ∀ y ≥ (1 : ℝ), x^2 * (fderiv ℝ (fun (x' : ℝ) => fderiv ℝ (fun (x'' : ℝ) => f x'' y) x' x) x) + y^2 * (fderiv ℝ (fun (y' : ℝ) => fderiv ℝ (fun (y'' : ℝ) => f x y'') y' y) y) = x * y)}),
    let m_f : ℝ := ⨅ (s : ℝ) (hs : s ≥ 1), (f (s + 1) (s + 1) - f (s + 1) s - f s (s + 1) + f s s) in
    m_f = Real.log 4 - 1/2 ∧ ∀ (g : ℝ → ℝ → ℝ) (hg : g ∈ {f : ℝ → ℝ → ℝ | ∀ x ≥ (1 : ℝ), ∀ y ≥ (1 : ℝ), ContDiff ℝ 2 (fun (p : ℝ × ℝ) => f p.1 p.2) ∧
    (∀ x ≥ (1 : ℝ), ∀ y ≥ (1 : ℝ), x * fderiv ℝ (fun (x' : ℝ) => f x' y) x + y * fderiv ℝ (fun (y' : ℝ) => f x y') y = x * y * Real.log (x * y)) ∧
    (∀ x ≥ (1 : ℝ), ∀ y ≥ (1 : ℝ), x^2 * (fderiv ℝ (fun (x' : ℝ) => fderiv ℝ (fun (x'' : ℝ) => f x'' y) x' x) x) + y^2 * (fderiv ℝ (fun (y' : ℝ) => fderiv ℝ (fun (y'' : ℝ) => f x y'') y' y) y) = x * y)}),
    let m_g : ℝ := ⨅ (s : ℝ) (hs : s ≥ 1), (g (s + 1) (s + 1) - g (s + 1) s - g s (s + 1) + g s s) in
    m_g = m_f := sorry

theorem coefficient_expansion (n k : ℕ) (hn : n ≥ 0) (hk : k ≥ 0) :
    let Q (n k : ℕ) := Polynomial.coeff ((1 + X + X ^ 2 + X ^ 3) ^ n) k
    in Q n k = ∑ j in Finset.range (k + 1), (Nat.choose n j) * (Nat.choose n (k - 2 * j)) := sorry

theorem integral_diverges (f : ℝ → ℝ) (hpos : ∀ x, 0 ≤ x → 0 ≤ f x) (hstrict_decr : ∀ x y, 0 ≤ x → x < y → f y < f x) (hcont : ContinuousOn f (Set.Ici 0)) (hlim : Filter.Tendsto f Filter.atTop (nhds 0)) : 
    ¬ Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (λ t : ℝ => ∫ x in (0 : ℝ)..t, (f x - f (x + 1)) / f x) := sorry

theorem sum_of_divisors_divisible_by_24 (n : ℕ) (hn_pos : n > 0) (h_div : 24 ∣ n + 1) : 24 ∣ ∑ d in (Nat.divisors n), d := sorry

theorem exists_linear_recurrence : ∀ (x : ℕ → ℝ) (hx : ∀ n, x n ≠ 0), (∀ n ≥ 1, (x n)^2 - x (n - 1) * x (n + 1) = 1) → ∃ (a : ℝ), ∀ n ≥ 1, x (n + 1) = a * x n - x (n - 1) := sorry

theorem inequality_of_geometric_means (n : ℕ) (hn : n > 0) (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∏ i, a i) ^ (1 / (n : ℝ)) + (∏ i, b i) ^ (1 / (n : ℝ)) ≤ (∏ i, (a i + b i)) ^ (1 / (n : ℝ)) := sorry

theorem triangle_inequality_with_circumradius (a b c R : ℝ) (Triangle : Set (ℝ × ℝ)) (h_Triangle : Triangle = {A : ℝ × ℝ | ∃ (B C : ℝ × ℝ), A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ (Prod.fst A, Prod.snd A) ≠ (Prod.fst B, Prod.snd B) ∧ (Prod.fst A, Prod.snd A) ≠ (Prod.fst C, Prod.snd C) ∧ (Prod.fst B, Prod.snd B) ≠ (Prod.fst C, Prod.snd C) ∧ let distAB := Real.sqrt (((Prod.fst B - Prod.fst A) ^ 2) + ((Prod.snd B - Prod.snd A) ^ 2)) in let distAC := Real.sqrt (((Prod.fst C - Prod.fst A) ^ 2) + ((Prod.snd C - Prod.snd A) ^ 2)) in let distBC := Real.sqrt (((Prod.fst C - Prod.fst B) ^ 2) + ((Prod.snd C - Prod.snd B) ^ 2)) in (distAB = a ∧ distAC = b ∧ distBC = c) ∨ (distAB = a ∧ distAC = c ∧ distBC = b) ∨ (distAB = b ∧ distAC = a ∧ distBC = c) ∨ (distAB = b ∧ distAC = c ∧ distBC = a) ∨ (distAB = c ∧ distAC = a ∧ distBC = b) ∨ (distAB = c ∧ distAC = b ∧ distBC = a)}) (h_circle : ∃ (center : ℝ × ℝ), ∀ (vertex : ℝ × ℝ), vertex ∈ Triangle → Real.sqrt (((Prod.fst vertex - Prod.fst center) ^ 2) + ((Prod.snd vertex - Prod.snd center) ^ 2)) = R) : a * b * c ≥ 2 * R := sorry

theorem equal_elements (n : ℕ) (a : ℕ → ℤ) (S : Set ℕ := {i | 1 ≤ i ∧ i ≤ 2 * n + 1}) 
    (h : ∀ k ∈ S, ∃ (A B : Finset ℕ), A.card = n ∧ B.card = n ∧ A ∩ B = ∅ ∧ A ∪ B = S.erase k ∧ 
        (∑ i in A, a i) = (∑ i in B, a i)) : 
    ∀ i ∈ S, ∀ j ∈ S, a i = a j := sorry

