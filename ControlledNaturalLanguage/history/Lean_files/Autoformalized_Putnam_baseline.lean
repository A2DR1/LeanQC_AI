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

theorem four_of_five_points_form_convex_quadrilateral (P : Finset (ℝ × ℝ)) (hP : P.card = 5) (hNoThreeColinear : ∀ (S : Finset (ℝ × ℝ)), S ⊆ P → S.card = 3 → ¬Collinear (Set.univ : Set (ℝ × ℝ)) (fun x => x) (S : Set (ℝ × ℝ))) : ∀ (Q : Finset (ℝ × ℝ)), Q ⊆ P → Q.card = 4 → ConvexHull ℝ (Q : Set (ℝ × ℝ)) = ↑Q := sorry

theorem function_form {I : Set ℝ} (hI : I = Set.Ici 0 ∨ ∃ b, I = Set.Ico 0 b) (f : ℝ → ℝ) (hf : ∀ x ∈ I, x > 0 → (∫ t in 0..x, f t) / x = Real.sqrt (f 0 * f x)) : ∃ (a : ℝ) (c : ℝ), a > 0 ∧ (∀ x ∈ I, f x = a / (1 - c * x)^2) ∧ (c > 0 → ∃ b, I = Set.Ico 0 b ∧ b = 1 / c) ∧ (c ≤ 0 → I = Set.Ici 0) := sorry

theorem ceva_area_ratio (ABC : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2))) (k : ℝ) (hk : k ≠ 0 ∧ k ≠ -1) :
    ∀ (P : {x // x ∈ Affine.Segment ℝ (ABC.points 1) (ABC.points 2)})
    (Q : {x // x ∈ Affine.Segment ℝ (ABC.points 2) (ABC.points 0)})
    (R : {x // x ∈ Affine.Segment ℝ (ABC.points 0) (ABC.points 1)}),
    (‖(↑Q - ABC.points 2)‖ / ‖(ABC.points 0 - ↑Q)‖ = k) →
    (‖(↑R - ABC.points 0)‖ / ‖(ABC.points 1 - ↑R)‖ = k) →
    (‖(↑P - ABC.points 1)‖ / ‖(ABC.points 2 - ↑P)‖ = k) →
    let AP := Affine.Subspace.affineSpan ℝ {ABC.points 0, ↑P};
    let BQ := Affine.Subspace.affineSpan ℝ {ABC.points 1, ↑Q};
    let CR := Affine.Subspace.affineSpan ℝ {ABC.points 2, ↑R};
    let U := Classical.choose (Affine.Subspace.inter_nonempty_of_inter_nonempty_of_sup_le 
      (Affine.Subspace.affineSpan ℝ {ABC.points 1, ↑Q}) (Affine.Subspace.affineSpan ℝ {ABC.points 2, ↑R}));
    let V := Classical.choose (Affine.Subspace.inter_nonempty_of_inter_nonempty_of_sup_le 
      (Affine.Subspace.affineSpan ℝ {ABC.points 2, ↑R}) (Affine.Subspace.affineSpan ℝ {ABC.points 0, ↑P}));
    let W := Classical.choose (Affine.Subspace.inter_nonempty_of_inter_nonempty_of_sup_le 
      (Affine.Subspace.affineSpan ℝ {ABC.points 0, ↑P}) (Affine.Subspace.affineSpan ℝ {ABC.points 1, ↑Q}));
    let UVW : Affine.Triangle ℝ (EuclideanSpace ℝ (Fin 2)) := ⟨![U, V, W]⟩;
    (Affine.Triangle.area UVW) / (Affine.Triangle.area ABC) = (k - 1)^2 / (k^2 + k + 1) := sorry

theorem derivative_bound {f : ℝ → ℝ} {a b : ℝ} (hab : b - a ≥ 2) (hf_cont : ∀ x ∈ Icc a b, ContinuousAt f x) (hf_diff : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) (hf_bound : ∀ x ∈ Icc a b, |f x| ≤ 1) (hf_second_bound : ∀ x ∈ Icc a b, |f'' x| ≤ 1) : ∀ x ∈ Icc a b, |f' x| ≤ 2 := sorry

theorem sum_choose_mul_k_sq_eq (n : ℕ) : ∑ k in Finset.range (n + 1), Nat.choose n k * k^2 = n * (n + 1) * 2^(n - 2) := sorry

theorem positive_rationals_characterization (S : Set ℚ) (h_add : ∀ a b ∈ S, a + b ∈ S) (h_mul : ∀ a b ∈ S, a * b ∈ S) (h_trich : ∀ r : ℚ, (r ∈ S) ∨ (-r ∈ S) ∨ (r = 0)) (h_zero : (0 : ℚ) ∉ S) : S = {q : ℚ | 0 < q} := sorry

theorem falling_factorial_binomial (x y : ℕ) (n : ℕ) : (x + y) ^ (n) = ∑ k in Finset.range (n + 1), Nat.choose n k * x ^ (k) * y ^ (n - k) := sorry

theorem exists_increasing_function_from_reals_to_set_of_groups : ∃ (S : Set (Set ℕ)) (f : ℝ → Set ℕ), (∀ (a b : ℝ), a < b → f a ⊆ f b) := sorry

theorem convex_set_bounded {S : Set (ℝ × ℝ)} (hconv : Convex ℝ S) (h0 : (0, 0) ∈ S) 
  (hray : ∀ θ : ℝ, ∃ r : ℝ, ∀ t : ℝ, t ≥ r → (t * Real.cos θ, t * Real.sin θ) ∉ S) 
  (h : (∃ ε > 0, Metric.ball (0, 0) ε ⊆ S) ∨ IsClosed S) : Metric.Bounded S := sorry

theorem sum_inequality (n : ℕ) (hn : n > 1) : (3 * ↑n + 1) / (2 * ↑n + 2) < ∑ k in Finset.range n, (↑k / ↑n) ^ n ∧ ∑ k in Finset.range n, (↑k / ↑n) ^ n < 2 := sorry

theorem trigonometric_sum_form {n : ℕ} {a b : Fin (n + 1) → ℝ} (f : ℝ → ℝ) (hdef : ∀ x, f x = ∑ k in Finset.range (n + 1), (a k * Real.sin (k * x) + b k * Real.cos (k * x))) (hbounded : ∀ x ∈ Set.Icc 0 (2 * Real.pi), |f x| ≤ 1) (hmax : ∃ (x : Fin (2 * n) → ℝ), (∀ i, x i ∈ Set.Icc 0 (2 * Real.pi)) ∧ (∀ i, |f (x i)| = 1) ∧ StrictMono x) : ∃ (α : ℝ), ∀ x, f x = Real.cos (n * x + α) := sorry

theorem multiplicative_increasing_function_is_identity (f : ℕ → ℕ) (h_mono : StrictMono f) (h_f2 : f 2 = 2) (h_mult : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n) : ∀ n, f n = n := sorry

theorem diff_eq_solution (n : ℕ) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ici 1)) :
  ∀ (y : ℝ → ℝ), (∀ k < n, (iteratedDerivWithin k y (Set.Ici 1) 1 = 0)) → 
  (∀ x ≥ 1, (Finset.prod (Finset.range n) (fun k => (x * deriv (fun x => deriv (fun x => y x) x) x - k))) y x = f x) →
  ∀ x ≥ 1, y x = ∫ t in (1:ℝ)..x, (x - t)^(n - 1) * f t / ((Nat.factorial (n - 1)) * t^n) := sorry

theorem limsup_inequality (a : ℕ → ℝ) (ha : ∀ n, a n > 0) : 
  (Filter.limsup (fun n ↦ n * ((1 + a (n + 1)) / a n - 1)) Filter.atTop) ≥ 1 ∧ 
  ∀ c > 1, ¬(Filter.limsup (fun n ↦ n * ((1 + a (n + 1)) / a n - 1)) Filter.atTop) ≥ c := sorry

theorem ellipse_chord_property {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ell : Set E) (hEll : IsEllipse ℝ ell) (U V : E) (hU : U ∈ ell) (hV : V ∈ ell) (hUV : U ≠ V) (M : E) (hM : M = midpoint ℝ U V) (A B C D : E) (hA : A ∈ ell) (hB : B ∈ ell) (hC : C ∈ ell) (hD : D ∈ ell) (hAB : M ∈ segment ℝ A B) (hCD : M ∈ segment ℝ C D) (P : E) (hP : P ∈ line ℝ U V ∩ line ℝ A C) (Q : E) (hQ : Q ∈ line ℝ U V ∩ line ℝ B D) : M = midpoint ℝ P Q := sorry

theorem polynomial_condition (a : ℤ) (h : ∃ (x : ℤ), x^2 - x + a = x^13 + x + 90) : a = 2 := sorry

theorem set_S_dense_in_P (f : ℝ) (hf : f > 0) : ∀ ε > 0, ∃ m n : ℤ, |(2:ℝ)^m * (3:ℝ)^n - f| < ε := sorry

theorem satisfies_functional_equation (f : ℝ → ℝ) (hf : ∀ x, DifferentiableAt ℝ f x) (hf' : ∀ x, DifferentiableAt ℝ (deriv f) x) (h : ∀ x y, f x ^ 2 - f y ^ 2 = f (x + y) * f (x - y)) : (∃ (A k : ℝ), ∀ u, f u = A * Real.sinh (k * u)) ∨ (∃ (A : ℝ), ∀ u, f u = A * u) ∨ (∃ (A k : ℝ), ∀ u, f u = A * Real.sin (k * u)) := sorry

theorem limit_n_times_a_n_zero (a : ℕ → ℝ) (h₁ : ∀ n k, n ≤ k ∧ k ≤ 2 * n → 0 ≤ a k ∧ a k ≤ 100 * a n) (h₂ : Summable a) : Filter.Tendsto (fun n => ↑n * a n) Filter.atTop (nhds 0) := sorry

theorem segment_closure_stabilizes {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (h_dim : finrank ℝ E ≤ 3) (A₀ : Set E) (hA₀ : A₀.Nonempty) : 
let S (A : Set E) := {x : E | ∃ a b ∈ A, x ∈ segment ℝ a b};
let A₁ := S A₀;
let A₂ := S A₁;
A₂ = ⋂ (n ≥ 2), S^[n] A₀ := sorry

theorem min_max_distance_ratio (A1 A2 A3 A4 A5 A6 : ℝ × ℝ) (h_distinct : Pairwise fun i j => A1 ≠ A2 ∧ A1 ≠ A3 ∧ A1 ≠ A4 ∧ A1 ≠ A5 ∧ A1 ≠ A6 ∧ A2 ≠ A3 ∧ A2 ≠ A4 ∧ A2 ≠ A5 ∧ A2 ≠ A6 ∧ A3 ≠ A4 ∧ A3 ≠ A5 ∧ A3 ≠ A6 ∧ A4 ≠ A5 ∧ A4 ≠ A6 ∧ A5 ≠ A6) : ∃ D d, (∀ i j, dist (A1) (A2) ≤ D ∧ dist (A1) (A3) ≤ D ∧ dist (A1) (A4) ≤ D ∧ dist (A1) (A5) ≤ D ∧ dist (A1) (A6) ≤ D ∧ dist (A2) (A3) ≤ D ∧ dist (A2) (A4) ≤ D ∧ dist (A2) (A5) ≤ D ∧ dist (A2) (A6) ≤ D ∧ dist (A3) (A4) ≤ D ∧ dist (A3) (A5) ≤ D ∧ dist (A3) (A6) ≤ D ∧ dist (A4) (A5) ≤ D ∧ dist (A4) (A6) ≤ D ∧ dist (A5) (A6) ≤ D) ∧ (∀ i j, dist (A1) (A2) ≥ d ∧ dist (A1) (A3) ≥ d ∧ dist (A1) (A4) ≥ d ∧ dist (A1) (A5) ≥ d ∧ dist (A1) (A6) ≥ d ∧ dist (A2) (A3) ≥ d ∧ dist (A2) (A4) ≥ d ∧ dist (A2) (A5) ≥ d ∧ dist (A2) (A6) ≥ d ∧ dist (A3) (A4) ≥ d ∧ dist (A3) (A5) ≥ d ∧ dist (A3) (A6) ≥ d ∧ dist (A4) (A5) ≥ d ∧ dist (A4) (A6) ≥ d ∧ dist (A5) (A6) ≥ d) ∧ D / d ≥ Real.sqrt 3 := sorry

theorem no_continuous_function_satisfies_conditions (α : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) (hpos : ∀ x ∈ Set.Icc 0 1, f x > 0) (h1 : ∫ x in 0..1, f x = 1) (h2 : ∫ x in 0..1, x * f x = α) (h3 : ∫ x in 0..1, x^2 * f x = α^2) : False := sorry

theorem dense_points_split_interval_sum (x : ℕ → ℝ) (h_dense : Dense (range x)) (h_mem : ∀ n, x n ∈ Set.Ioo 0 1) (h_split : ∀ n, ∃ (a b : ℝ), x n ∈ Set.Ioo (x (n-1)) (x (n+1)) ∧ a = x n - x (n-1) ∧ b = x (n+1) - x n) : ∑' n, (x n - x (n-1)) * (x (n+1) - x n) * (x (n+1) - x (n-1)) = 1/3 := sorry

theorem sequence_eventually_periodic (u : ℕ → ℤ) (h_bounded : ∃ M, ∀ n, |u n| ≤ M) (h_rec : ∀ n ≥ 4, u n = (u (n-1) + u (n-2) + u (n-3) * u (n-4)) / (u (n-1) * u (n-2) + u (n-3) + u (n-4))) : ∃ N p, p > 0 ∧ ∀ n ≥ N, u (n + p) = u n := sorry

theorem exists_uniform_bound_for_series_inequality : ∃ (k : ℝ), ∀ (a : ℕ → ℝ), (∀ n, a n > 0) → (∑' n, (n : ℝ) / (∑ i in Finset.range n, a i)) ≤ k * (∑' n, 1 / a n) := sorry

theorem distance_ratio_rational (S : Finset ℝ) (hS : ∀ (x y : ℝ), x ∈ S → y ∈ S → ∃ (t : ℝ), y = x + t) (k : ℝ) (hk : k = iSup (fun (p : ℝ × ℝ) ↦ if p.1 ∈ S ∧ p.2 ∈ S then ‖p.2 - p.1‖ else 0)) (a b : ℝ) (ha : ∃ (x y : ℝ), x ∈ S ∧ y ∈ S ∧ ‖y - x‖ = a) (hb : ∃ (x y : ℝ), x ∈ S ∧ y ∈ S ∧ ‖y - x‖ = b) (h : ∀ (d : ℝ), (∃ (x y : ℝ), x ∈ S ∧ y ∈ S ∧ ‖y - x‖ = d) → d < k → ∀ (z w : ℝ), z ∈ S ∧ w ∈ S ∧ ‖w - z‖ = d → ∃ (u v : ℝ), u ∈ S ∧ v ∈ S ∧ ‖v - u‖ = d ∧ (u ≠ z ∨ v ≠ w))) : ∃ (m n : ℤ), b ≠ 0 → a = (m / n) * b := sorry

theorem limit_of_bn_over_n (a : ℕ → ℝ) (ha : ∀ n, a n > 0) (hsum : ∃ L : ℝ, HasSum (λ n, 1 / a n) L) (b : ℕ → ℕ) (hb : ∀ n, b n = Finset.card (Finset.filter (λ k, a k ≤ n) Finset.univ)) : Filter.Tendsto (λ n, (b n : ℝ) / n) Filter.atTop (nhds 0) := sorry

theorem maximal_intersecting_family_has_half_power_set (S : Type*) [Fintype S] (P : Set (Set S)) (hP₁ : ∀ A B ∈ P, (A ∩ B).Nonempty) (hP₂ : ∀ Q : Set (Set S), Q ⊃ P → ∃ A B ∈ Q, (A ∩ B).Empty) : P.card = 2^(Fintype.card S - 1) := sorry

theorem limit_at_infty_of_limit_n_alpha (f : ℝ → ℝ) (hf : Continuous f) (h : ∀ α > 0, Filter.Tendsto (fun n ↦ f (n * α)) Filter.atTop (nhds 0)) : Filter.Tendsto f Filter.atTop (nhds 0) := sorry

theorem sphere_partition_by_great_circles (n : ℕ) : 
  Fintype.card {s : Set (Sphere (Fin 3) ℝ) | ∃ (C : Finset (GreatCircle (Fin 3) ℝ)), 
  Finset.card C = n ∧ GeneralPosition C ∧ s ∈ ConnectedComponents (Sphere (Fin 3) ℝ \ ⋃ c ∈ C, c)} = n^2 - n + 2 := sorry

theorem sum_inv_lcm_of_strictly_increasing_positive_sequence (a : ℕ → ℕ) (ha_strict_mono : StrictMono a) (ha_pos : ∀ n, a n > 0) : Summable fun n => 1 / (Nat.lcm (Finset.range (n + 1)).sup a) := sorry

theorem no_partition_of_unit_disk_into_congruent_disjoint_sets : ¬∃ (A B : Set (ℝ × ℝ)), A ⊆ Metric.ball (0, 0) 1 ∧ B ⊆ Metric.ball (0, 0) 1 ∧ A ∪ B = Metric.ball (0, 0) 1 ∧ A ∩ B = ∅ ∧ ∃ (f : (ℝ × ℝ) → (ℝ × ℝ)), Isometry f ∧ f '' A = B := sorry

theorem angle_CAB_is_pi_over_15 (A B C : ℝ × ℝ) (h_triangle : AffineIndependent ℝ ![A, B, C]) 
  (h_angle_CAB_lt_angle_BCA : ∠ C A B < ∠ B C A) 
  (h_angle_BCA_lt_pi_div_2 : ∠ B C A < π / 2) 
  (h_pi_div_2_lt_angle_ABC : π / 2 < ∠ A B C) 
  (P : ℝ × ℝ) (hP : P ∈ affineSpan ℝ ![B, C]) 
  (hAP_is_ext_bisector : ∃ (AP : Ray ℝ (ℝ × ℝ)), AP.source = A ∧ P ∈ AP.toDirLine ∧ AP.toDirLine = (Angle.extAngleBisector (∠ C A B)).toDirLine) 
  (Q : ℝ × ℝ) (hQ : Q ∈ affineSpan ℝ ![C, A]) 
  (hBQ_is_ext_bisector : ∃ (BQ : Ray ℝ (ℝ × ℝ)), BQ.source = B ∧ Q ∈ BQ.toDirLine ∧ BQ.toDirLine = (Angle.extAngleBisector (∠ A B C)).toDirLine) 
  (h_AP_eq_AB : dist A P = dist A B) 
  (h_BQ_eq_AB : dist B Q = dist A B) : ∠ C A B = π / 15 := sorry

theorem sum_binomial_identity (n : ℕ) : ∑ r in Finset.range (Nat.floor ((n - 1)/2) + 1), ((↑(n - 2 * r) / ↑n * Nat.choose n r : ℝ))^2 = ↑(1 / n) * ↑(Nat.choose (2 * n - 2) (n - 1)) := sorry

theorem exp_avg_equiv (a : ℕ → ℝ) (α : ℂ) : 
    (Filter.Tendsto (λ n ↦ (∑ k in Finset.range n, Complex.exp (Complex.I * ↑(a k))) / ↑n) Filter.atTop (nhds α)) ↔ 
    (Filter.Tendsto (λ n ↦ (∑ k in Finset.range n, Complex.exp (Complex.I * ↑(a (k^2)))) / ↑(n^2)) Filter.atTop (nhds α)) := sorry

theorem dance_party {Guy Girl : Type*} [Fintype Guy] [Fintype Girl] (Dances : Guy → Girl → Prop) (h₁ : ∀ (b : Guy), ¬ ∀ (g : Girl), Dances b g) (h₂ : ∀ (g : Girl), ∃ (b : Guy), Dances b g) : ∃ (g h : Girl) (b c : Guy), Dances b g ∧ Dances c h ∧ ¬ Dances b h ∧ ¬ Dances c g := sorry

theorem count_valid_permutations (n : ℕ) : Fintype.card {f : Fin n → Fin n | Function.Bijective f ∧ ∀ (i : Fin n), i ≠ 0 → ∃ (j : Fin n), j < i ∧ (f j = f i - 1 ∨ f j = f i + 1)} = 2 ^ (n - 1) := sorry

theorem tangent_condition (m : ℝ) (hm : 1 < m) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : 
(∃ x y : ℝ, 0 < x ∧ 0 < y ∧ u * x + v * y = 1 ∧ x^m + y^m = 1 ∧ u = m * x^(m - 1) ∧ v = m * y^(m - 1)) ↔ 
(∃ n : ℝ, u^n + v^n = 1 ∧ 1 / m + 1 / n = 1) := sorry

theorem limit_of_integral_sum (n : ℕ) (hn : n > 0) (f : ℕ → ℝ → ℝ) (hf : ∀ k, ∀ x, 0 ≤ f k x ∧ f k x ≤ 1) :
  Tendsto (fun n ↦ ∫ x in 0..1, (Real.cos (π / (2 * ↑n))) ^ 2 * (∑ k in Finset.range n, f k x)) atTop (𝓝 (1/2)) := sorry

theorem sum_win_loss_squared_eq (n : ℕ) (hn : n > 1) (P : Fin n → Type*) (game : ∀ i j : Fin n, i ≠ j → P i × P j → Bool) (wr lr : Fin n → ℕ) (hwr : ∀ r, wr r = Finset.card (Finset.univ.filter (λ j => game r j (Ne.symm (Fin.ne_of_ne_of_eq (by simp) (by simp))) (P r, P j)))) (hlr : ∀ r, lr r = Finset.card (Finset.univ.filter (λ j => ¬game j r (Fin.ne_of_ne_of_eq (by simp) (by simp)) (P j, P r)))) : ∑ i : Fin n, (wr i)^2 = ∑ i : Fin n, (lr i)^2 := sorry

theorem exists_three_right_triangles_with_area_double_perimeter : 
  ∃! (T : Finset { t : ℕ × ℕ × ℕ // t.1^2 + t.2^2 = t.3^2 ∧ t.1 * t.2 = 2 * (t.1 + t.2 + t.3) }), 
  T.card = 3 ∧ ∀ (t : { t : ℕ × ℕ × ℕ // t.1^2 + t.2^2 = t.3^2 ∧ t.1 * t.2 = 2 * (t.1 + t.2 + t.3) }), 
  t ∈ T ∨ (∃ (k : ℕ), t = ⟨(k * t.1.1, k * t.1.2, k * t.1.3), _⟩) := sorry

theorem f_limit_neg (x : ℝ) (hx : x < 0) : ¬∃ (L : ℝ), Filter.Tendsto (fun n ↦ f x n) Filter.atTop (nhds L) := sorry

theorem exists_triangle_free_graph (E V : ℕ) (h : 4 * E ≤ V ^ 2) : ∃ (G : SimpleGraph (Fin V)), G.edgeFinset.card = E ∧ ¬SimpleGraph.CliqueFree G 3 := sorry

theorem four_points_collinear_or_concyclic (A B C D : EuclideanSpace ℝ (Fin 2)) (h₁ : A ≠ B) (h₂ : A ≠ C) (h₃ : A ≠ D) (h₄ : B ≠ C) (h₅ : B ≠ D) (h₆ : C ≠ D) (h : ∀ (γ₁ γ₂ : Set (EuclideanSpace ℝ (Fin 2))), IsCircle γ₁ → A ∈ γ₁ → B ∈ γ₁ → IsCircle γ₂ → C ∈ γ₂ → D ∈ γ₂ → ∃ p, p ∈ γ₁ ∧ p ∈ γ₂) : Collinear ℝ ({A, B, C, D} : Set (EuclideanSpace ℝ (Fin 2))) ∨ ∃ (γ : Set (EuclideanSpace ℝ (Fin 2))), IsCircle γ ∧ A ∈ γ ∧ B ∈ γ ∧ C ∈ γ ∧ D ∈ γ := sorry

theorem product_relation (a : ℕ → ℕ) (h_a : ∀ n, a n = if n % 2 = 0 then n / 2 else (n - 1) / 2) (f : ℕ → ℕ) (h_f : ∀ n, f n = ∑ k in Finset.range n, a k) (x y : ℕ) (h_xy : x > y) : x * y = f (x + y) - f (x - y) := sorry

theorem inradius_inequality (a b c r : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hr : r > 0) 
  (triangle_ineq : a + b > c ∧ b + c > a ∧ c + a > b) 
  (area_formula : r * (a + b + c) / 2 = Real.sqrt (((a + b + c) / 2) * ((a + b + c) / 2 - a) * ((a + b + c) / 2 - b) * ((a + b + c) / 2 - c))) : 
  let p := (a + b + c) / 2;
  1 / (p - a)^2 + 1 / (p - b)^2 + 1 / (p - c)^2 ≥ 1 / r^2 := sorry

theorem limit_product_sequence (x : ℕ → ℝ) (h₀ : x 1 ∈ Set.Ioo 0 1) (h_rec : ∀ n, x (n + 1) = x n * (1 - x n)) : Filter.Tendsto (fun n ↦ ↑n * x n) Filter.atTop (nhds 1) := sorry

theorem nth_non_square (n : ℕ) : ∃ k : ℤ, List.get (List.sort (· ≤ ·) (List.filter (fun m => ¬∃ p : ℕ, p * p = m) (List.range (n + (Nat.sqrt n + 1)^2 + 1)))) ⟨n, sorry⟩ = n + k ∧ |k - Nat.sqrt n| ≤ 1 := sorry

theorem exists_multiplier_for_linear_local_operator (T : (ℝ → ℝ) → (ℝ → ℝ)) (hT_linear : ∀ (a b : ℝ) (f g : ℝ → ℝ), Continuous f → Continuous g → T (a • f + b • g) = a • T f + b • T g) (hT_local : ∀ (f g : ℝ → ℝ), Continuous f → Continuous g → (∀ x ∈ I, f x = g x) → ∀ x ∈ I, T f x = T g x) (hT_cont : ∀ f, Continuous f → Continuous (T f)) : ∃ (f : ℝ → ℝ), Continuous f ∧ ∀ (g : ℝ → ℝ), Continuous g → ∀ x, T g x = f x * g x := sorry

theorem nested_sqrt_converges_to_three : Filter.Tendsto (fun n => Real.sqrt (1 + (n + 1) * Real.sqrt (1 + (n + 2) * Real.sqrt (1 + (n + 3) * Real.sqrt (1 + (n + 4) * Real.sqrt (1 + (n + 5) * (1 : ℝ))))))) Filter.atTop (nhds 3) := sorry

theorem sum_of_squared_lengths_bounded (L : Set (ℝ × ℝ)) (h_convex : Convex ℝ L) (h_subset : L ⊆ Icc (0, 0) (1, 1)) : 
∀ (s : Finset (ℝ × ℝ)) (h : ∀ p ∈ s, p ∈ L), ∑ p in s, ‖p‖^2 ≤ 4 := sorry

theorem consecutive_ten_contains_coprime (n : ℕ) : ∃ k ∈ Finset.Icc n (n + 9), ∀ m ∈ Finset.Icc n (n + 9), m ≠ k → Nat.Coprime k m := sorry

theorem sum_condition (p : ℕ → ℝ) (hp : ∀ n, p n > 0) (hsum : Summable fun n => 1 / p n) : 
  Summable fun n => (n^2 * p n) / (∑ i in Finset.range (n + 1), p i)^2 := sorry

theorem increasing_list_property (m n : ℕ) (a : ℕ → ℕ) (h : StrictMono a) (k : ℕ) (hk : k = m * n + 1) : (∃ s : Finset ℕ, s.card = m + 1 ∧ ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬(a i ∣ a j)) ∨ (∃ s : Finset ℕ, s.card = n + 1 ∧ ∀ i ∈ s, ∀ j ∈ s, i < j → a i ∣ a j) := sorry

theorem exists_simple_closed_shape (n : ℕ) (h : n ≥ 3) (points : Finset (Fin n × ℝ × ℝ)) 
  (no_collinear : ∀ (i j k : Fin n), i ≠ j → j ≠ k → i ≠ k → ¬Collinear ({(points i).2.1, (points j).2.1, (points k).2.1} : Set (ℝ × ℝ))) : 
  ∃ (f : Fin n → ℝ × ℝ), Function.Injective f ∧ ∀ i, f i ∈ (points i).2.1 ∧ 
  ∃ (γ : ℝ → ℝ × ℝ), SimpleClosedCurve γ ∧ ∀ i, ∃ t, γ t = f i := sorry

theorem solution_bounded_at_infinity {y : ℝ → ℝ} (h : ∀ x, y'' x + Real.exp x * y x = 0) : Filter.Tendsto (fun x => ‖y x‖) Filter.atTop (nhds 0) := sorry

theorem sum_abs_coeff_le_one (n : ℕ) (a : Fin n → ℝ) (h : ∀ x : ℝ, |∑ i in Finset.range n, a ⟨i, Nat.lt_succ_of_lt (Finset.mem_range.1 i.2)⟩ * Real.sin ((i + 1) * x)| ≤ |Real.sin x|) : ∑ i in Finset.range n, |(i + 1) * a ⟨i, Nat.lt_succ_of_lt (Finset.mem_range.1 i.2)⟩| ≤ 1 := sorry

theorem part_b (S : ℕ → ℕ) (hS0 : S 0 = 1) (hS : ∀ n ≥ 1, S n = Fintype.card {M : Matrix (Fin n) (Fin n) ℕ // (∀ i j, M i j = M j i) ∧ (∀ j, ∑ i, M i j = 1)}) : (∑' n, S n * (x^n / n! : ℝ)) = Real.exp (x + x^2 / 2) := sorry

theorem smallest_quadratic_coefficient_with_two_roots_in_01 : 
  ∃ a : ℕ, a = 5 ∧ (∀ b c : ℤ, ∃ x₁ x₂ : ℝ, x₁ ∈ Set.Ioo 0 1 ∧ x₂ ∈ Set.Ioo 0 1 ∧ x₁ ≠ x₂ ∧ 
    ∀ x : ℝ, x = x₁ ∨ x = x₂ → a * x^2 - b * x + c = 0) ∧ 
  (∀ a' : ℕ, a' < 5 → ¬ ∀ b c : ℤ, ∃ x₁ x₂ : ℝ, x₁ ∈ Set.Ioo 0 1 ∧ x₂ ∈ Set.Ioo 0 1 ∧ x₁ ≠ x₂ ∧ 
    ∀ x : ℝ, x = x₁ ∨ x = x₂ → a' * x^2 - b * x + c = 0) := sorry

theorem no_solution_for_lambda_gt_half (λ : ℝ) (hλ : λ > 1/2) : ¬∃ (u : ℝ → ℝ), ∀ (x : ℝ), x ∈ Set.Icc 0 1 → u x = 1 + λ * ∫ y in Set.Icc x 1, u y * u (y - x) := sorry

theorem exists_points_distance_one_of_area_gt_pi_div_four (S : Set (ℝ × ℝ)) (h_convex : Convex ℝ S) (h_area : volume S > Real.pi / 4) : ∃ x y ∈ S, dist x y = 1 := sorry

theorem max_sign_patterns (a1 a2 a3 a4 b1 b2 b3 b4 : ℝ) (h : a1 * b2 - a2 * b1 ≠ 0) :
  ∃ (x : ℝ × ℝ × ℝ × ℝ), x.1 ≠ 0 ∧ x.2.1 ≠ 0 ∧ x.2.2.1 ≠ 0 ∧ x.2.2.2 ≠ 0 ∧
  a1 * x.1 + a2 * x.2.1 + a3 * x.2.2.1 + a4 * x.2.2.2 = 0 ∧
  b1 * x.1 + b2 * x.2.1 + b3 * x.2.2.1 + b4 * x.2.2.2 = 0 ∧
  Fintype.card (Finset.univ : Finset (Fin 8 → Bool)) = 8 := sorry

theorem hexagon_midpoints_equilateral {r : ℝ} (h : 0 < r) (A B C D E F : ℝ × ℝ) (h_circle : ∀ (P : ℝ × ℝ), P ∈ [A, B, C, D, E, F] → dist P (0, 0) = r) (h_sides : dist A B = r ∧ dist C D = r ∧ dist E F = r) : let M := midpoint ℝ B C; let N := midpoint ℝ D E; let P := midpoint ℝ F A; dist M N = dist N P ∧ dist N P = dist P M := sorry

theorem part_b (p r : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1) (x y : ℝ) :
  (p * x + (1 - p) * y) * (r * x + (1 - r) * y) = α * x^2 + β * x * y + γ * y^2 →
  max (max α β) γ ≥ 4/9 := sorry

theorem integral_limit_of_periodic_products (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (hf_per : ∀ x, f (x + 1) = f x) (hg_per : ∀ x, g (x + 1) = g x) : Filter.Tendsto (fun (n : ℕ) => ∫ x in 0..1, f x * g (n * x)) Filter.atTop (nhds (∫ x in 0..1, f x * ∫ x in 0..1, g x)) := sorry

theorem locker_problem (n : ℕ) : ∀ (k : ℕ), k ∈ Finset.range (n + 1) → (Nat.sqrt k) ^ 2 = k ↔ ∃ (m : ℕ), m * m = k := sorry

theorem binomial_expansion_sum (n : ℕ) : ∑ k in Finset.range n, (2 - 1) ^ (-(n - k)) * Nat.choose n k = 1 / 2 := sorry

theorem exists_point_with_gradient_bound (f : ℝ → ℝ → ℝ) (h₁ : ∀ x y, x^2 + y^2 ≤ 1 → ∃ fxy, f x y = fxy) (h₂ : ∀ x y, x^2 + y^2 ≤ 1 → |f x y| ≤ 1) (h₃ : ∀ x y, x^2 + y^2 ≤ 1 → DifferentiableAt ℝ (fun x' ↦ f x' y) x) (h₄ : ∀ x y, x^2 + y^2 ≤ 1 → DifferentiableAt ℝ (fun y' ↦ f x y') y) : ∃ x₀ y₀, x₀^2 + y₀^2 < 1 ∧ ((deriv (fun x' ↦ f x' y₀) x₀)^2 + (deriv (fun y' ↦ f x₀ y') y₀)^2 ≤ 16) := sorry

theorem integral_representation : (↑22 / ↑7 - Real.pi) = ∫ x in (0:ℝ)..1, (x^4 * (1 - x)^4) / (1 + x^2) := sorry

theorem exists_rational_approximation (a b c d e f : ℤ) (h : a * d ≠ b * c) (ε : ℝ) (hε : ε > 0) : ∃ (r s : ℚ), |(r * ↑a + s * ↑b) - ↑e| > 0 ∧ |(r * ↑a + s * ↑b) - ↑e| < ε ∧ |(r * ↑c + s * ↑d) - ↑f| > 0 ∧ |(r * ↑c + s * ↑d) - ↑f| < ε := sorry

theorem exists_subset_list (S : Finset α) : ∃ (l : List (Finset α)), 
  l.head? = some ∅ ∧ 
  List.Nodup l ∧ 
  ∀ t ∈ l, t ⊆ S ∧ 
  ∀ i : Fin (l.length - 1), 
    (l.get i).1 ⊆ (l.get (i + 1)).1 ∧ Finset.card ((l.get (i + 1)).1 \ (l.get i).1) = 1 ∨ 
    (l.get (i + 1)).1 ⊆ (l.get i).1 ∧ Finset.card ((l.get i).1 \ (l.get (i + 1)).1) = 1 := sorry

theorem sum_sq_distances_le_n_sq (n : ℕ) (points : Fin n → {x : ℝ × ℝ × ℝ | x.1^2 + x.2.1^2 + x.2.2^2 = 1}) : 
∑ i j : Fin n, ‖(points i).val - (points j).val‖^2 ≤ n^2 := sorry

theorem supremum_derivative_at_zero : 
  sSup {c : ℝ | ∃ (P : ℝ → ℝ) (a b : ℝ), (∀ x, P x = a * x^2 + b * x + (1 - a - b)) ∧ (∀ x ∈ Set.Icc 0 1, |P x| ≤ 1) ∧ |deriv P 0| = c} = 8 := sorry

theorem real_root_polynomials_with_coeffs_pm1 :
  ∀ (n : ℕ) (p : ℝ[X]), n ≥ 1 → 
  (∃ (a : ℕ → ℤ), (∀ i, i ≤ n → a i = 1 ∨ a i = -1) ∧ 
  p = ∑ i in Finset.range (n + 1), Polynomial.C (↑(a i)) * Polynomial.X ^ (n - i)) → 
  Polynomial.Splits (RingHom.id ℝ) p → 
  p ∈ {Polynomial.C 1 * (Polynomial.X - 1), Polynomial.C (-1) * (Polynomial.X - 1),
       Polynomial.C 1 * (Polynomial.X + 1), Polynomial.C (-1) * (Polynomial.X + 1),
       Polynomial.C 1 * (Polynomial.X^2 + Polynomial.X - 1), Polynomial.C (-1) * (Polynomial.X^2 + Polynomial.X - 1),
       Polynomial.C 1 * (Polynomial.X^2 - Polynomial.X - 1), Polynomial.C (-1) * (Polynomial.X^2 - Polynomial.X - 1),
       Polynomial.C 1 * (Polynomial.X^3 + Polynomial.X^2 - Polynomial.X - 1), Polynomial.C (-1) * (Polynomial.X^3 + Polynomial.X^2 - Polynomial.X - 1),
       Polynomial.C 1 * (Polynomial.X^3 - Polynomial.X^2 - Polynomial.X + 1), Polynomial.C (-1) * (Polynomial.X^3 - Polynomial.X^2 - Polynomial.X + 1)} := sorry

theorem min_prob_eq_sum_diff_max_prob (X Y : Ω → ℤ) [ProbabilitySpace Ω] (k : ℤ) (p1 := ℙ (X = k)) (p2 := ℙ (Y = k)) (p3 := ℙ (max X Y = k)) : ℙ (min X Y = k) = p1 + p2 - p3 := sorry

theorem product_of_two_in_large_subset {G : Type*} [Group G] [Fintype G] (A : Set G) (hA : Fintype.card A > Fintype.card G / 2) (g : G) : ∃ a b ∈ A, g = a * b := sorry

theorem integral_substitution {f : ℝ → ℝ} (hf : Continuous f) (hint : Integrable f) : ∫ (x : ℝ), f (x - 1 / x) = ∫ (x : ℝ), f x := sorry

theorem count_special_matrices (p : ℕ) [Fact (Nat.Prime p)] : 
  Fintype.card {M : Matrix (Fin 2) (Fin 2) (ZMod p) | M 0 0 + M 1 1 = 1 ∧ M 0 0 * M 1 1 - M 0 1 * M 1 0 = 0} = p^2 + p := sorry

theorem not_countable_cover_of_compact_rational_sets (K : ℕ → Set ℚ) (h_compact : ∀ n, IsCompact (K n)) : ¬ ∀ (C : Set ℚ), IsCompact C → ∃ n, C ⊆ K n := sorry

theorem polynomial_range_cases (f : ℝ × ℝ → ℝ) (hf : ∃ (p : ℝ[X] × ℝ[X]), ∀ (xy : ℝ × ℝ), f xy = p.1 xy.1 + p.2 xy.2) : Set.range f = {f (0, 0)} ∨ (∃ (a : ℝ), Set.range f = Set.Ici a) ∨ (∃ (a : ℝ), Set.range f = Set.Iic a) ∨ Set.range f = Set.univ := sorry

theorem determinant_special_matrix (n : ℕ) : Matrix.det (Matrix.of (fun (i j : Fin n) => ↑|(i : ℤ) - (j : ℤ)|)) = (-1 : ℤ) ^ (n - 1) * (n - 1) * 2 ^ (n - 2) := sorry

theorem integral_eq_sum : ∫ (x : ℝ) in 0..1, x^x = ∑' (n : ℕ), (-1)^(n+1) * (n : ℝ)^(-(n : ℝ)) := sorry

theorem diff_eq_solution_behavior (u : ℝ → ℝ) (hu : Continuous u) (x y : ℝ → ℝ) (hx : ∀ t, HasDerivAt (x ·) (-2 * y t + u t) t) (hy : ∀ t, HasDerivAt (y ·) (-2 * x t + u t) t) : (x 0 ≠ y 0 → ∀ t, x t ≠ 0 ∨ y t ≠ 0) ∧ (x 0 = y 0 → ∀ T > 0, ∃ u₀ : ℝ → ℝ, Continuous u₀ ∧ (∀ t, HasDerivAt (x ·) (-2 * y t + u₀ t) t) ∧ (∀ t, HasDerivAt (y ·) (-2 * x t + u₀ t) t) ∧ x T = 0 ∧ y T = 0) := sorry

theorem seq_limit {X : Type*} [NormedAddCommGroup X] {x : ℕ → X} {y : ℕ → X} (h : ∀ n ≥ 2, y n = x (n - 1) + 2 • x n) {L : X} (hy : Filter.Tendsto y Filter.atTop (nhds L)) : ∃ M : X, Filter.Tendsto x Filter.atTop (nhds M) := sorry

theorem sum_divisors_divides_24 (n : ℕ) (h : (n + 1) ∣ 24) : (∑ d in Nat.divisors n, d) ∣ 24 := sorry

theorem three_subgroups_can_cover_finite_group : ∃ (G : Type*) [Group G] [Fintype G] (H K L : Subgroup G), H ≠ ⊤ ∧ K ≠ ⊤ ∧ L ≠ ⊤ ∧ (∀ x : G, x ∈ H ∨ x ∈ K ∨ x ∈ L) := sorry

theorem sequence_limit_condition (T : ℕ → ℝ) (h_rec : ∀ n ≥ 1, T n * T (n + 1) = n) (h_lim : Tendsto (fun n => T n / T (n + 1)) atTop (𝓝 1)) : Real.pi * (T 1)^2 = 2 := sorry

theorem exists_rectangle_covering_curve (Γ : Set (ℝ × ℝ)) (hΓ : IsConnected Γ) (hlength : arcLength Γ = 1) : ∃ (R : Set (ℝ × ℝ)), IsRectangle R ∧ IsClosed R ∧ Γ ⊆ R ∧ area R = 1/4 := sorry

theorem k_over_x_tends_to_zero {a : ℕ → ℝ} (ha_pos : ∀ n, a n > 0) (ha_mono : StrictMono a) (ha_sum : Summable fun n ↦ 1 / a n) : ∀ ε > 0, ∃ x₀ > 0, ∀ x ≥ x₀, |(Nat.card {n | a n ≤ x}) / x| < ε := sorry

theorem matrix_mult_inverse {A : Matrix (Fin 3) (Fin 2) ℝ} {B : Matrix (Fin 2) (Fin 3) ℝ} 
  (hAB : A * B = !![8, 2, -2; 2, 5, 4; -2, 4, 5]) : B * A = !![9, 0; 0, 9] := sorry

theorem power_series_coefficients_nonzero_or_infinitely_many_zero (a b : ℝ) (ha : a > 0) (hb : b > 0) : 
(∀ n : ℕ, (Function.update (fun n => if Even n then (-1) ^ (n / 2) * b ^ n else 0) 0 (1 : ℝ)) n * a ^ n / n.factorial ≠ 0) ∨ 
(∃ infinite_set : Set ℕ, Set.Infinite infinite_set ∧ ∀ n ∈ infinite_set, (Function.update (fun n => if Even n then (-1) ^ (n / 2) * b ^ n else 0) 0 (1 : ℝ)) n * a ^ n / n.factorial = 0) := sorry

theorem exists_delta_for_nonzero_expression (A B C D E F G : ℝ) (h : B^2 - 4 * A * C < 0) :
    ∃ δ > 0, ∀ (x y : ℝ), 0 < x^2 + y^2 ∧ x^2 + y^2 < δ → A * x^2 + B * x * y + C * y^2 + D * x^3 + E * x^2 * y + F * x * y^2 + G * y^3 ≠ 0 := sorry

theorem max_trailing_nonzero_digit_run_in_squares : 
  (∃ (n : ℕ), n ≠ 0 ∧ ∃ (d : ℕ), d ∈ Set.Ioo 0 10 ∧ ∀ k ∈ Set.Icc 1 3, (n^2 / 10^(k-1)) % 10 = d) ∧ 
  (¬∃ (n : ℕ), n ≠ 0 ∧ ∃ (d : ℕ), d ∈ Set.Ioo 0 10 ∧ ∀ k ∈ Set.Icc 1 4, (n^2 / 10^(k-1)) % 10 = d) ∧ 
  (IsLeast {n : ℕ | n ≠ 0 ∧ ∃ (d : ℕ), d ∈ Set.Ioo 0 10 ∧ ∀ k ∈ Set.Icc 1 3, (n^2 / 10^(k-1)) % 10 = d} 38) := sorry

theorem diff_convergence_implies_normalized_convergence (x : ℕ → ℝ) (h : Tendsto (fun n ↦ x n - x (n - 2)) atTop (𝓝 0)) : Tendsto (fun n ↦ (x n - x (n - 1)) / ↑n) atTop (𝓝 0) := sorry

theorem limit_product_expression : Filter.Tendsto (fun (n : ℕ) => (1 / (n : ℝ)^4) * ∏ i in Finset.range (2 * n), (n^2 + i^2 : ℝ)^(1 / (n : ℝ))) Filter.atTop (nhds (Real.exp (2 * Real.log 5 - 4 + 2 * Real.arctan 2))) := sorry

theorem polynomial_average_eq (H : Polynomial ℝ) (hdeg : H.degree ≤ 3) (T : ℝ) (hT : T > 0) : 
    (1 / (2 * T)) * ∫ (t : ℝ) in -T..T, H t = (1 / 2) * (H (-T / Real.sqrt 3) + H (T / Real.sqrt 3)) := sorry

theorem projection_of_closed_set_is_closed {S : Set (ℝ × ℝ)} (hS : IsClosed S) (a b : ℝ) (hab : a < b) (hS_bounded : ∀ (p : ℝ × ℝ), p ∈ S → a < p.1 ∧ p.1 < b) : IsClosed (Prod.snd '' S) := sorry

theorem second_derivative_lower_bound (x : ℝ → ℝ) (hx : ContDiffOn ℝ 2 x (Set.Icc 0 1)) (hx0 : x 1 - x 0 = 1) (hx'0 : HasDerivAt x (x' 0) 0 ∧ x' 0 = 0) (hx'1 : HasDerivAt x (x' 1) 1 ∧ x' 1 = 0) (hx'bdd : ∀ t ∈ Set.Icc 0 1, |x' t| ≤ 3/2) : ∃ t ∈ Set.Icc 0 1, |x'' t| ≥ 9/2 := sorry

theorem continuous_iff_continuous_u_n_comp (F : ℝ → ℝ) : Continuous F ↔ ∀ (n : ℕ), Continuous (fun x ↦ if x ≤ -↑n then -↑n else if x ≤ ↑n then x else ↑n ∘ F) := sorry

theorem quadrilateral_tangential_implies_cyclic {a b c d : ℝ} (h₁ : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0) (h₂ : ∃ (K : ℝ), K = Real.sqrt (a * b * c * d)) (h₃ : ∃ (r : ℝ), ∀ (x : ℝ), x ∈ {a, b, c, d} → r = (K / x)) : ∃ (R : ℝ), ∀ (x : ℝ), x ∈ {a, b, c, d} → R = (a * b * c * d) / (4 * K) := sorry

