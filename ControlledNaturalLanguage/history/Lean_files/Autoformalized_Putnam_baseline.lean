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

theorem convex_quadrilateral_from_five_points (P : Finset (ℝ × ℝ)) (hP : P.card = 5) (hNoColinear : ∀ (S : Finset (ℝ × ℝ)), S ⊆ P → S.card = 3 → ¬Collinear S) : ∃ (Q : Finset (ℝ × ℝ)), Q ⊆ P ∧ Q.card = 4 ∧ ConvexHull ℝ (Q : Set (ℝ × ℝ)) = ConvexHull ℝ (Q : Set (ℝ × ℝ)) := sorry

theorem function_with_average_geometric_mean (f : ℝ → ℝ) (I : Set ℝ) (hI : I = Set.Ico 0 (if 0 < c then 1 / c else ∞)) (h0 : f 0 = a) (ha : 0 < a) (h_avg : ∀ x ∈ I, 0 < x → (∫ t in 0..x, f t) / x = Real.sqrt (f 0 * f x)) : ∀ x ∈ I, f x = a / (1 - c * x) ^ 2 := sorry

theorem triangle_area_ratio (ABC : Triangle ℝ (NormedAddCommGroup.toSeminormedAddCommGroup)) (k : ℝ) (hk : k > 0) (P : ℝ × ℝ) (Q : ℝ × ℝ) (R : ℝ × ℝ) (hP : P ∈ segment ℝ (Triangle.points ABC).2 (Triangle.points ABC).3) (hQ : Q ∈ segment ℝ (Triangle.points ABC).3 (Triangle.points ABC).1) (hR : R ∈ segment ℝ (Triangle.points ABC).1 (Triangle.points ABC).2) (hAQ_QC : dist (Triangle.points ABC).1 Q / dist Q (Triangle.points ABC).3 = k) (hBR_RA : dist (Triangle.points ABC).2 R / dist R (Triangle.points ABC).1 = k) (hCP_PB : dist (Triangle.points ABC).3 P / dist P (Triangle.points ABC).2 = k) : ∃ UVW : Triangle ℝ (NormedAddCommGroup.toSeminormedAddCommGroup), (area UVW) / (area ABC) = (k - 1)^2 / (k^2 + k + 1) := sorry

theorem derivative_bound (f : ℝ → ℝ) (a b : ℝ) (hab : b - a ≥ 2) (hf : ∀ x ∈ Set.Icc a b, |f x| ≤ 1) (hf'' : ∀ x ∈ Set.Icc a b, |f'' x| ≤ 1) : ∀ x ∈ Set.Icc a b, |f' x| ≤ 2 := sorry

theorem sum_choose_mul_k_sq_eq (n : ℕ) : ∑ k in Finset.range (n + 1), (Nat.choose n k) * k^2 = n * (n + 1) * 2^(n - 2) := sorry

theorem positive_rationals_characterization (S : Set ℚ) (h_add : ∀ a b ∈ S, a + b ∈ S) (h_mul : ∀ a b ∈ S, a * b ∈ S) (h_trichotomy : ∀ r : ℚ, (r ∈ S) ∨ (-r ∈ S) ∨ (r = 0)) : S = {q : ℚ | q > 0} := sorry

theorem falling_factorial_binomial {α : Type*} [CommSemiring α] (x y : α) (n : ℕ) : (x + y)^(n) = ∑ k in Finset.range (n + 1), Nat.choose n k * x^(k) * y^(n - k) := sorry

theorem exists_increasing_function_from_reals_to_nat_sets : ∃ (f : ℝ → Set ℕ), ∀ (a b : ℝ), a < b → f a ⊆ f b := sorry

theorem convex_set_bounded {S : Set (ℝ × ℝ)} (hConv : Convex ℝ S) (h0 : (0, 0) ∈ S) 
(hRay : ∀ θ : ℝ, ∃ r : ℝ, ∀ t : ℝ, t ≥ r → (t * Real.cos θ, t * Real.sin θ) ∉ S) 
(hIntOrClosed : (interior S).Nonempty ∧ (0, 0) ∈ interior S ∨ IsClosed S) : 
Bounded S := sorry

theorem sum_bounds (n : ℕ) (hn : n > 1) : (3 * ↑n + 1) / (2 * ↑n + 2) < ∑ k in Finset.range n, (↑k / ↑n) ^ n ∧ ∑ k in Finset.range n, (↑k / ↑n) ^ n < 2 := sorry

theorem fourier_sum_maxima {n : ℕ} {a b : ℕ → ℝ} (f : ℝ → ℝ) (hdef : ∀ x, f x = ∑ k in Finset.range (n + 1), a k * Real.sin (k * x) + b k * Real.cos (k * x)) (hbounded : ∀ x ∈ Set.Icc 0 (2 * Real.pi), |f x| ≤ 1) (x : ℕ → ℝ) (hx : StrictMono x) (hx_range : ∀ i ∈ Finset.range (2 * n + 1), x i ∈ Set.Icc 0 (2 * Real.pi)) (hmax : ∀ i ∈ Finset.range (2 * n + 1), |f (x i)| = 1) : ∃ c, ∀ x, f x = Real.cos (n * x + c) := sorry

theorem multiplicative_increasing_sequence_is_identity (f : ℕ → ℕ) (h_mono : StrictMono f) (h_pos : ∀ n, f n > 0) (h_f2 : f 2 = 2) (h_mul : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n) : ∀ n, f n = n := sorry

theorem differential_equation_solution (n : ℕ) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ici 1)) :
  ∀ (y : ℝ → ℝ), (∏ k in Finset.range n, fun δ => δ - k) (fun x => x * deriv y x) = f →
  (∀ k < n, deriv^[k] y 1 = 0) →
  y = fun x => ∫ t in (1:ℝ)..x, (x - t)^(n - 1) * f t / (Nat.factorial (n - 1) * t^n) := sorry

theorem limsup_sequence_bound (a : ℕ → ℝ) (ha : ∀ n, a n > 0) : 
  (Filter.limsup (fun n => n * ((1 + a (n + 1)) / a n - 1)) Filter.atTop) ≥ 1 ∧ 
  ∀ c > 1, ¬(Filter.limsup (fun n => n * ((1 + a (n + 1)) / a n - 1)) Filter.atTop) ≥ c := sorry

theorem midpoint_property_of_ellipse {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ell : Set E) (hEll : IsEllipse ell) (U V A B C D M P Q : E) (hU : U ∈ ell) (hV : V ∈ ell) (hM : M = midpoint ℝ U V) (hA : A ∈ ell) (hB : B ∈ ell) (hC : C ∈ ell) (hD : D ∈ ell) (hAB : M ∈ segment ℝ A B) (hCD : M ∈ segment ℝ C D) (hP : P ∈ line ℝ U V ∧ P ∈ line ℝ A C) (hQ : Q ∈ line ℝ U V ∧ Q ∈ line ℝ B D) : M = midpoint ℝ P Q := sorry

theorem find_a (x : ℤ) (h : x^2 - x + a = x^13 + x + 90) : a = 2 := sorry

theorem set_S_dense_in_P : Dense {x : ℝ | ∃ m n : ℤ, x = 2^m * 3^n} := sorry

theorem diff_func_satisfying_identity (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f)) : (∀ x y : ℝ, f x ^ 2 - f y ^ 2 = f (x + y) * f (x - y)) → (∃ (A k : ℝ), (∀ u : ℝ, f u = A * Real.sinh (k * u)) ∨ (∀ u : ℝ, f u = A * u) ∨ (∀ u : ℝ, f u = A * Real.sin (k * u))) := sorry

theorem limit_n_times_a_n_zero (a : ℕ → ℝ) (h₁ : ∀ n k, n ≤ k → k ≤ 2 * n → 0 ≤ a k ∧ a k ≤ 100 * a n) (h₂ : Summable a) : Filter.Tendsto (fun n ↦ ↑n * a n) Filter.atTop (nhds 0) := sorry

theorem segment_closure_stabilizes {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (h_dim : FiniteDimensional.finrank ℝ E ≤ 3) (A₀ : Set E) (hA₀ : A₀.Nonempty) : let S (A : Set E) := {x : E | ∃ a b ∈ A, x ∈ segment ℝ a b}; let A₁ := S A₀; let A₂ := S A₁; ∀ n ≥ 2, S (A₂) = A₂ := sorry

theorem min_max_distance_ratio (A1 A2 A3 A4 A5 A6 : ℝ × ℝ) (h_distinct : Pairwise fun i j => (i ≠ j → (A1, A2, A3, A4, A5, A6).nth i ≠ (A1, A2, A3, A4, A5, A6).nth j)) : ∃ D d, (∀ i j, i ≠ j → dist (A1, A2, A3, A4, A5, A6).nth i (A1, A2, A3, A4, A5, A6).nth j ≤ D) ∧ (∀ i j, i ≠ j → d ≤ dist (A1, A2, A3, A4, A5, A6).nth i (A1, A2, A3, A4, A5, A6).nth j) ∧ D / d ≥ Real.sqrt 3 := sorry

theorem no_continuous_positive_function_with_moments (α : ℝ) : ¬∃ (f : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) ∧ (∀ x ∈ Set.Icc 0 1, f x > 0) ∧ (∫ x in 0..1, f x = 1) ∧ (∫ x in 0..1, x * f x = α) ∧ (∫ x in 0..1, x^2 * f x = α^2) := sorry

theorem sum_a_b_a_plus_b_eq_one_third (x : ℕ → ℝ) (hx : ∀ n, x n ∈ Set.Ioo (0 : ℝ) 1) (hsplit : ∀ n ≥ 1, ∃ (a b : ℝ), a > 0 ∧ b > 0 ∧ a + b = (Finset.range n).sup' (Finset.nonempty_range_succ n) (fun k ↦ x k) - (Finset.range n).inf' (Finset.nonempty_range_succ n) (fun k ↦ x k) ∧ x n ∈ Set.Ioo ((Finset.range n).inf' (Finset.nonempty_range_succ n) (fun k ↦ x k)) ((Finset.range n).sup' (Finset.nonempty_range_succ n) (fun k ↦ x k))) ∧ (∀ n ≥ 1, ∃ (a b : ℝ), a > 0 ∧ b > 0 ∧ a + b = (Finset.range n).sup' (Finset.nonempty_range_succ n) (fun k ↦ x k) - (Finset.range n).inf' (Finset.nonempty_range_succ n) (fun k ↦ x k) ∧ x n ∈ Set.Ioo ((Finset.range n).inf' (Finset.nonempty_range_succ n) (fun k ↦ x k)) ((Finset.range n).sup' (Finset.nonempty_range_succ n) (fun k ↦ x k)))) : HasSum (fun n ↦ let ⟨a, b, _, _, hab, _⟩ := Classical.choose (hsplit (n + 1) (Nat.succ_pos n)); a * b * (a + b)) (1 / 3) := sorry

theorem eventually_periodic (u : ℕ → ℕ) (h_bounded : ∃ B, ∀ n, u n ≤ B) (h_rec : ∀ n ≥ 4, u n = (u (n-1) + u (n-2) + u (n-3) * u (n-4)) / (u (n-1) * u (n-2) + u (n-3) + u (n-4))) : ∃ N P, ∀ n ≥ N, u (n + P) = u n := sorry

theorem exists_uniform_bound_for_series_ratio : ∃ (k : ℝ), ∀ (a : ℕ → ℝ), (∀ n, a n > 0) → (∑' n, (n / (∑ i in Finset.range (n + 1), a i))) ≤ k * (∑' n, 1 / a n) := sorry

theorem rational_ratio_of_distances (S : Finset ℝ) (hS : ∃ (l : ℝ), ∀ x ∈ S, ∃ t : ℝ, x = l * t) (k : ℝ) (hk : k = sSup (pairwiseDistances S)) (hd : ∀ d < k, ∃ p q ∈ S, dist p q = d) (a b : ℝ) (ha : ∃ p q ∈ S, dist p q = a ∧ p ≠ q) (hb : ∃ r s ∈ S, dist r s = b ∧ r ≠ s) : ∃ m n : ℤ, b ≠ 0 ∧ a / b = Rat.mk m n := sorry

theorem limit_of_count_ratio (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hsum : ∃ L, Tendsto (fun N ↦ ∑ n in Finset.range N, 1 / a n) atTop (𝓝 L)) (b : ℕ → ℕ) (hb : ∀ n, b n = Finset.card (Finset.filter (fun k ↦ a k ≤ n) (Finset.range (n + 1)))) : Tendsto (fun n ↦ ↑(b n) / ↑n) atTop (𝓝 0) := sorry

theorem maximal_intersecting_family_size {S : Type*} [Fintype S] (P : Set (Set S)) (hP₁ : ∀ A B ∈ P, (A ∩ B).Nonempty) (hP₂ : ∀ A ∉ P, ∃ B ∈ P, (A ∩ B).Empty) : Nat.card P = 2 ^ (Nat.card S - 1) := sorry

theorem continuous_tendsto_zero_at_infinity (f : ℝ → ℝ) (hf : Continuous f) (h : ∀ α > 0, Filter.Tendsto (fun n ↦ f (↑n * α)) Filter.atTop (nhds 0)) : Filter.Tendsto f Filter.atTop (nhds 0) := sorry

theorem sphere_regions_from_great_circles (n : ℕ) : Fintype.card {r : Set (Sphere (3 : ℕ)) | ∃ (C : Finset (GreatCircle (3 : ℕ))), Finset.card C = n ∧ GeneralPosition C ∧ r ∈ ConnectedComponents (Sphere (3 : ℕ) \ ⋃ c ∈ C, c)} = n^2 - n + 2 := sorry

theorem sum_inv_lcm_of_increasing_pos_seq (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n) : 
    Summable fun n => 1 / (Nat.lcm (Finset.range n).sup (fun k => a (k + 1))) := sorry

theorem unit_disk_not_congruent_partition : ¬∃ (A B : Set (ℝ × ℝ)), A ∪ B = Metric.ball (0, 0) 1 ∧ A ∩ B = ∅ ∧ ∃ (f : ℝ × ℝ → ℝ × ℝ), Isometry f ∧ f '' A = B := sorry

theorem find_angle_CAB (A B C P Q : ℝ × ℝ) (hABC : AffineIndependent ℝ ![A, B, C]) (hCAB : ∠ C A B < ∠ B C A) (hBCA : ∠ B C A < Real.pi / 2) (hABC_gt : ∠ A B C > Real.pi / 2) (hAP : P ∈ line[ℝ, B, C]) (hAQ : Q ∈ line[ℝ, C, A]) (hAP_eq : dist A P = dist A B) (hBQ_eq : dist B Q = dist A B) (hAB_eq : dist A B = dist B Q) : ∠ C A B = Real.pi / 15 := sorry

theorem sum_square_binomial_coefficient (n : ℕ) : ∑ r in Finset.range (Nat.floor ((n - 1) / 2) + 1), ((↑(n - 2 * r) / ↑n * Nat.choose n r)^2) = ↑(1 / n) * Nat.choose (2 * n - 2) (n - 1) := sorry

theorem exp_avg_convergence_iff_squares_convergence (a : ℕ → ℝ) (α : ℂ) : 
  Filter.Tendsto (fun n : ℕ ↦ (Finset.sum (Finset.range n) (fun k ↦ Complex.exp (Complex.I * ↑(a k))) / ↑n)) Filter.atTop (nhds α) ↔ 
  Filter.Tendsto (fun n : ℕ ↦ (Finset.sum (Finset.range (n^2)) (fun k ↦ Complex.exp (Complex.I * ↑(a k))) / ↑(n^2))) Filter.atTop (nhds α) := sorry

theorem dance_party {G H : Type*} [Fintype G] [Fintype H] (Dances : G → H → Prop) 
  (h1 : ∀ (b : G), ¬ ∀ (h : H), Dances b h) 
  (h2 : ∀ (h : H), ∃ (b : G), Dances b h) : 
  ∃ (g h : H) (b c : G), Dances b g ∧ Dances c h ∧ ¬ Dances b h ∧ ¬ Dances c g := sorry

theorem count_valid_orderings (n : ℕ) : Fintype.card {l : List ℕ // l.length = n ∧ l.Nodup ∧ ∀ (i : ℕ) (hi : i ∈ l.tail), ∃ j ∈ l.take (l.indexOf i), j = i - 1 ∨ j = i + 1} = 2 ^ (n - 1) := sorry

theorem tangent_condition (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (m : ℝ) (hm : 1 < m) (x y : ℝ) (hline : u * x + v * y = 1) (hcurve : x^m + y^m = 1) : (∃ n : ℝ, u^(n:ℝ) + v^(n:ℝ) = 1 ∧ 1/m + 1/n = 1) ↔ ∃ (t : ℝ), x = t * u^(1/(m-1)) ∧ y = t * v^(1/(m-1)) ∧ t^(m:ℝ) * (u^(m/(m-1)) + v^(m/(m-1))) = 1 := sorry

theorem integral_cos_squared_limit (n : ℕ) : 
  Filter.Tendsto (fun n ↦ ∫ (x : Fin n → ℝ) in (Set.pi Set.univ fun _ ↦ Set.Icc 0 1), Real.cos (Real.pi / (2 * ↑n) * (∑ i, x i)) ^ 2) 
  Filter.atTop (nhds (1/2)) := sorry

theorem round_robin_wins_losses (n : ℕ) (hn : n > 1) (players : Fin n → Type*) (games : ∀ (i j : Fin n), i ≠ j → Type*) (wins losses : Fin n → ℕ) (hgames : ∀ (i j : Fin n) (h : i ≠ j), (wins i = wins j + 1 ∧ losses j = losses i + 1) ∨ (wins j = wins i + 1 ∧ losses i = losses j + 1)) : ∑ r : Fin n, (wins r)^2 = ∑ r : Fin n, (losses r)^2 := sorry

theorem right_triangles_with_area_eq_twice_perimeter : ∃ (T : Finset (ℕ × ℕ × ℕ)), T.card = 3 ∧ ∀ (a b c : ℕ) (h : a^2 + b^2 = c^2) (h_area : a * b / 2 = 2 * (a + b + c)), (a, b, c) ∈ T ∨ (b, a, c) ∈ T := sorry

theorem f_limit_neg (x : ℝ) (hx : x < 0) : ¬∃ (L : ℝ), Filter.Tendsto (fun n => f x n) Filter.atTop (nhds L) := sorry

theorem exists_triangle_free_graph (V E : ℕ) (h : 4 * E ≤ V^2) : ∃ (G : SimpleGraph (Fin V)), G.edgeFinset.card = E ∧ ¬SimpleGraph.CliqueFree G 3 := sorry

theorem four_points_collinear_or_concyclic (A B C D : ℝ × ℝ) (hdistinct : A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D) (hintersect : ∀ (C1 : ℝ × ℝ) (r1 : ℝ), dist A C1 = r1 ∧ dist B C1 = r1 → ∀ (C2 : ℝ × ℝ) (r2 : ℝ), dist C C2 = r2 ∧ dist D C2 = r2 → ∃ p, dist p C1 = r1 ∧ dist p C2 = r2) : (∃ (l : ℝ × ℝ → ℝ × ℝ → Prop), Collinear l A B C D) ∨ (∃ (c : ℝ × ℝ) (r : ℝ), dist A c = r ∧ dist B c = r ∧ dist C c = r ∧ dist D c = r) := sorry

theorem fib_sum_diff (a : ℕ → ℕ) (ha : ∀ n, a n = if n % 2 = 0 then n / 2 else (n - 1) / 2) (f : ℕ → ℕ) (hf : ∀ n, f n = ∑ k in Finset.range n, a k) (x y : ℕ) (hxy : x > y) : x * y = f (x + y) - f (x - y) := sorry

theorem inradius_inequality (a b c r : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hr : r > 0) (h : a + b > c ∧ b + c > a ∧ c + a > b) (h_area : r * (a + b + c) / 2 = Real.sqrt ((a + b + c) / 2 * ((a + b + c) / 2 - a) * ((a + b + c) / 2 - b) * ((a + b + c) / 2 - c))) : let p := (a + b + c) / 2; 1 / (p - a)^2 + 1 / (p - b)^2 + 1 / (p - c)^2 ≥ 1 / r^2 := sorry

theorem sequence_limit (x : ℕ → ℝ) (h₀ : x 0 ∈ Set.Ioo 0 1) (h_rec : ∀ n, x (n + 1) = x n * (1 - x n)) : Filter.Tendsto (fun n => ↑n * x n) Filter.atTop (nhds 1) := sorry

theorem nth_non_square_eq_n_plus_round_sqrt (n : ℕ) : 
  (List.filter (fun k => ¬∃ m, m * m = k) (List.range (n + (Nat.sqrt n + 1) ^ 2))).get ⟨n, sorry⟩ = n + Nat.round (Real.sqrt n) := sorry

theorem exists_continuous_function_representation (T : (ℝ → ℝ) → (ℝ → ℝ)) (hT_linear : ∀ (a b : ℝ) (f g : ℝ → ℝ), T (a • f + b • g) = a • T f + b • T g) (hT_local : ∀ (f g : ℝ → ℝ) (I : Set ℝ), (∀ x ∈ I, f x = g x) → ∀ x ∈ I, T f x = T g x) : ∃ (f : ℝ → ℝ), Continuous f ∧ ∀ (g : ℝ → ℝ), Continuous g → ∀ x, T g x = f x * g x := sorry

theorem nested_sqrt_converges_to_three : Filter.Tendsto (fun n => Real.sqrt (1 + (n + 1) * Real.sqrt (1 + (n + 2) * Real.sqrt (1 + (n + 3) * Real.sqrt (1 + (n + 4) * Real.sqrt (1 + (n + 5) * Real.sqrt (1 + (n + 6) * Real.sqrt (1 + (n + 7) * Real.sqrt (1 + (n + 8) * Real.sqrt (1 + (n + 9) * Real.sqrt (1 + (n + 10) * Real.sqrt 1))))))))))) Filter.atTop (nhds 3) := sorry

theorem sum_of_squares_of_sides_le_four (L : Set ℝ × ℝ) (hL : Convex ℝ L) (hL_subset : L ⊆ Set.Icc 0 1 ×ˢ Set.Icc 0 1) : ∑ x in (boundary L).toFinset, (sideLength x)^2 ≤ 4 := sorry

theorem consecutive_ten_has_coprime (n : ℕ) : ∃ (k : ℕ), k ∈ Set.Icc n (n + 9) ∧ ∀ (m : ℕ), m ∈ Set.Icc n (n + 9) → m ≠ k → Nat.coprime k m := sorry

theorem sum_condition_convergence (p : ℕ → ℝ) (hp : ∀ n, p n > 0) (hsum : Summable fun n => 1 / p n) : 
  Summable fun n => (n^2 * p n) / (∑ k in Finset.range (n + 1), p k)^2 := sorry

theorem exists_increasing_or_decreasing_subsequence {m n : ℕ} (l : List ℕ) (hl : List.Sorted (· ≤ ·) l) (hpos : ∀ x ∈ l, 0 < x) : 
(∃ s ⊆ l, s.length = m + 1 ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬(a ∣ b)) ∨ 
(∃ s ⊆ l, s.length = n + 1 ∧ List.Sorted (· ∣ ·) s) := sorry

theorem exists_simple_closed_polygon (n : ℕ) (hn : n ≥ 3) (points : Finset (ℝ × ℝ)) 
(h_no_collinear : ∀ (p q r : ℝ × ℝ), p ∈ points → q ∈ points → r ∈ points → p ≠ q → p ≠ r → q ≠ r → ¬Collinear ℝ ![p, q, r]) :
∃ (polygon : List (ℝ × ℝ)), polygon.Nodup ∧ polygon.length = n ∧ (∀ p ∈ polygon, p ∈ points) ∧ 
SimplePolygon (mkPolygon polygon (by simp [hn])) := sorry

theorem bounded_solution_of_ode (y : ℝ → ℝ) (h : ∀ x, (deriv (deriv y) x) + Real.exp x * y x = 0) : ∃ M : ℝ, ∃ N : ℝ, ∀ x ≥ N, |y x| ≤ M := sorry

theorem fourier_series_coeff_bound (n : ℕ) (a : Fin n → ℝ) (h : ∀ (x : ℝ), |∑ i in Finset.range n, a i * Real.sin ((i + 1) * x)| ≤ |Real.sin x|) : ∑ i in Finset.range n, |(i + 1) * a i| ≤ 1 := sorry

theorem part_b (S : ℕ → ℕ) (hS0 : S 0 = 1) (hS : ∀ n ≥ 1, S n = Nat.card {M : Matrix (Fin n) (Fin n) ℕ // Matrix.IsSymm M ∧ ∀ j, ∑ i, M i j = 1}) : HasSum (fun n => (S n : ℝ) * x^n / n!) (Real.exp (x + x^2 / 2)) := sorry

theorem min_quadratic_coefficient (a b c : ℝ) (ha : a > 0) (h : ∃ x₁ x₂, x₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ x₂ ∈ Set.Ioo (0 : ℝ) 1 ∧ x₁ ≠ x₂ ∧ a * x₁^2 - b * x₁ + c = 0 ∧ a * x₂^2 - b * x₂ + c = 0) : a ≥ 5 ∧ (∃ b c, a = 5 ∧ ∃ x₁ x₂, x₁ ∈ Set.Ioo (0 : ℝ) 1 ∧ x₂ ∈ Set.Ioo (0 : ℝ) 1 ∧ x₁ ≠ x₂ ∧ 5 * x₁^2 - b * x₁ + c = 0 ∧ 5 * x₂^2 - b * x₂ + c = 0) := sorry

theorem no_solution_for_lambda_gt_half (λ : ℝ) (hλ : λ > 1/2) : ¬∃ (u : ℝ → ℝ), ∀ (x : ℝ), x ∈ Set.Icc 0 1 → u x = 1 + λ * ∫ y in Set.Icc x 1, u y * u (y - x) := sorry

theorem convex_set_area_gt_pi_div_four_has_points_one_apart {S : Set ℝ²} (hConv : Convex ℝ S) (hArea : volume S > π / 4) : ∃ x y ∈ S, dist x y = 1 := sorry

theorem max_sign_patterns (a1 a2 a3 a4 b1 b2 b3 b4 : ℝ) (h : a1 * b2 - a2 * b1 ≠ 0) : 
  Fintype.card {s : Fin 4 → SignType // ∃ (x : Fin 4 → ℝ), (∀ i, x i ≠ 0) ∧ 
  (a1 * x 0 + a2 * x 1 + a3 * x 2 + a4 * x 3 = 0) ∧ 
  (b1 * x 0 + b2 * x 1 + b3 * x 2 + b4 * x 3 = 0) ∧ 
  (∀ i, SignType.sign (x i) = s i)} ≤ 8 := sorry

theorem hexagon_midpoints_equilateral {r : ℝ} (h : 0 < r) (A B C D E F : ℝ × ℝ) (h_circ : ∀ (p : ℝ × ℝ), p ∈ {A, B, C, D, E, F} → ‖p‖ = r) (h_AB : ‖A - B‖ = r) (h_CD : ‖C - D‖ = r) (h_EF : ‖E - F‖ = r) : let M := (B + C) / 2; let N := (D + E) / 2; let P := (F + A) / 2; ‖M - N‖ = ‖N - P‖ ∧ ‖N - P‖ = ‖P - M‖ := sorry

theorem max_coeff_b (p r : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (hr : 0 ≤ r ∧ r ≤ 1) :
  max (max (p * r) (p * (1 - r) + r * (1 - p))) ((1 - p) * (1 - r)) ≥ 4/9 := sorry

theorem limit_of_integral_product_periodic {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hf_per : ∀ x, f (x + 1) = f x) (hg_per : ∀ x, g (x + 1) = g x) : Tendsto (fun n ↦ ∫ x in 0..1, f x * g (n * x)) atTop (𝓝 (∫ x in 0..1, f x * ∫ x in 0..1, g x)) := sorry

theorem locker_problem (n : ℕ) : ∀ (k : ℕ), k ∈ Finset.Icc 1 n → (Nat.sqrt k ^ 2 = k ↔ ∃ (m : ℕ), m ∈ Finset.Icc 1 n ∧ ∃ (t : ℕ), t ∈ Finset.Icc 1 n ∧ k = m * t ∧ (Finset.card (Finset.filter (fun d => d ∣ k) (Finset.Icc 1 k))).natMod 2 = 1)) := sorry

theorem sum_first_n_bits (n : ℕ) : ∑ k in Finset.range n, (1/2 : ℝ) ^ (k + 1) = 1/2 := sorry

theorem exists_point_with_gradient_bound (f : ℝ → ℝ → ℝ) (h_def : ∀ x y, x^2 + y^2 ≤ 1 → ∃ fxy, f x y = fxy) (h_bdd : ∀ x y (h : x^2 + y^2 ≤ 1), |f x y| ≤ 1) (h_diff : ∀ x y (h : x^2 + y^2 ≤ 1), DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) (x, y)) : ∃ x₀ y₀, x₀^2 + y₀^2 ≤ 1 ∧ ((deriv (fun x => f x y₀) x₀)^2 + (deriv (fun y => f x₀ y) y₀)^2) ≤ 16 := sorry

theorem twenty_two_sevenths_minus_pi_eq_integral : (22 : ℝ) / 7 - Real.pi = ∫ x in (0 : ℝ)..1, x^4 * (1 - x)^4 / (1 + x^2) := sorry

theorem exists_rational_approximation (a b c d e f : ℤ) (h : a * d ≠ b * c) (ε : ℝ) (hε : ε > 0) : ∃ (r s : ℚ), |(↑r * ↑a + ↑s * ↑b - ↑e)| > 0 ∧ |(↑r * ↑a + ↑s * ↑b - ↑e)| < ε ∧ |(↑r * ↑c + ↑s * ↑d - ↑f)| > 0 ∧ |(↑r * ↑c + ↑s * ↑d - ↑f)| < ε := sorry

theorem exists_subset_list_with_transition {α : Type*} [Fintype α] (S : Set α) :
∃ (l : List (Set α)), l.Nodup ∧ l.head? = some ∅ ∧ ∀ (i : Fin (l.length - 1)),
(∃ (x : α), l.get i = l.get (i.castSucc) \ {x}) ∨ (∃ (x : α), l.get i = insert x (l.get (i.castSucc))) := sorry

theorem sum_sq_distances_le_nsq (n : ℕ) (points : Fin n → EuclideanSpace ℝ (Fin 3)) 
  (h : ∀ i, ‖points i‖ = 1) : ∑ i j, ‖points i - points j‖^2 ≤ n^2 := sorry

theorem supremum_of_derivative_at_zero : 
  sSup {c : ℝ | ∃ (P : ℝ → ℝ), (∀ x, P x = P.coeff 0 + P.coeff 1 * x + P.coeff 2 * x^2) ∧ 
  (∀ x ∈ Set.Icc (0 : ℝ) 1, |P x| ≤ 1) ∧ c = |deriv P 0|} = 8 := sorry

theorem real_root_polynomials_with_coeff_1_or_neg1 :
  ∀ (n : ℕ) (p : Polynomial ℝ), n ≥ 1 →
  (∃ (a : ℕ → ℤ), (∀ i, a i = 1 ∨ a i = -1) ∧ p = ∑ i in Finset.range (n + 1), Polynomial.C (↑(a i)) * Polynomial.X ^ (n - i)) →
  (∀ (x : ℝ), Polynomial.IsRoot p x → Polynomial.IsRoot (Polynomial.C (1) * Polynomial.X ^ 1 - Polynomial.C (1)) x ∨
   Polynomial.IsRoot (Polynomial.C (1) * Polynomial.X ^ 1 + Polynomial.C (1)) x ∨
   Polynomial.IsRoot (Polynomial.C (1) * Polynomial.X ^ 2 + Polynomial.C (1) * Polynomial.X - Polynomial.C (1)) x ∨
   Polynomial.IsRoot (Polynomial.C (1) * Polynomial.X ^ 2 - Polynomial.C (1) * Polynomial.X - Polynomial.C (1)) x ∨
   Polynomial.IsRoot (Polynomial.C (1) * Polynomial.X ^ 3 + Polynomial.C (1) * Polynomial.X ^ 2 - Polynomial.C (1) * Polynomial.X - Polynomial.C (1)) x ∨
   Polynomial.IsRoot (Polynomial.C (1) * Polynomial.X ^ 3 - Polynomial.C (1) * Polynomial.X ^ 2 - Polynomial.C (1) * Polynomial.X + Polynomial.C (1)) x) := sorry

theorem prob_min_eq_k (X Y : Ω → ℕ) [ProbabilitySpace Ω] (k : ℕ) : 
  ℙ (fun ω ↦ min (X ω) (Y ω) = k) = ℙ (X = k) + ℙ (Y = k) - ℙ (fun ω ↦ max (X ω) (Y ω) = k) := sorry

theorem subset_covering_property (G : Type*) [Group G] [Fintype G] (A : Set G) (hA : Fintype.card A > Fintype.card G / 2) (g : G) : ∃ a b ∈ A, a * b = g := sorry

theorem integral_transform (f : ℝ → ℝ) (hf : Continuous f) (hint : Integrable f) : ∫ (x : ℝ), f (x - 1 / x) = ∫ (x : ℝ), f x := sorry

theorem count_special_matrices (p : ℕ) [Nat.Prime p] : Fintype.card {M : Matrix (Fin 2) (Fin 2) (ZMod p) | ∃ a b c d : ZMod p, M = !![a, b; c, d] ∧ a + d = 1 ∧ a * d - b * c = 0} = p^2 + p := sorry

theorem not_all_compact_sets_contained {ι : Type*} (K : ι → Set ℚ) (hK : ∀ n, IsCompact (K n)) : ¬ ∀ (C : Set ℚ), IsCompact C → ∃ n, C ⊆ K n := sorry

theorem polynomial_range_cases (f : ℝ × ℝ → ℝ) (hf : ∃ (p : ℝ[X][Y]), ∀ (x y : ℝ), f (x, y) = Polynomial.eval₂ (Polynomial.eval x) p y) : (∃ (c : ℝ), ∀ (x y : ℝ), f (x, y) = c) ∨ (∃ (a : ℝ), (∀ (x y : ℝ), f (x, y) ≥ a) ∧ ((∀ (b > a), ∃ (x y : ℝ), f (x, y) = b) ∨ (∀ (b ≥ a), ∃ (x y : ℝ), f (x, y) = b))) ∨ (∀ (b : ℝ), ∃ (x y : ℝ), f (x, y) = b) := sorry

theorem matrix_det_formula (n : ℕ) : Matrix.det (Matrix.of (fun i j : Fin n => ↑|(i : ℕ) - (j : ℕ)|)) = (-1) ^ (n - 1) * (n - 1) * 2 ^ (n - 2) := sorry

theorem integral_x_pow_x_eq_sum (n : ℕ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) : 
  ∫ (x : ℝ) in 0..1, x^x = ∑' (n : ℕ), (-1 : ℝ)^(n + 1) * (n : ℝ)^(-(n : ℝ)) := sorry

theorem differential_equation_property (u : ℝ → ℝ) (hu : Continuous u) (x y : ℝ → ℝ) (hx : ∀ t, HasDerivAt (x t) (deriv x t) t) (hy : ∀ t, HasDerivAt (y t) (deriv y t) t) (hdx : ∀ t, deriv x t = -2 * y t + u t) (hdy : ∀ t, deriv y t = -2 * x t + u t) : (x 0 ≠ y 0 → ∀ t, ¬(x t = 0 ∧ y t = 0)) ∧ (x 0 = y 0 → ∀ T > 0, ∃ u : ℝ → ℝ, Continuous u ∧ (∀ t, HasDerivAt (x t) (deriv x t) t) ∧ (∀ t, HasDerivAt (y t) (deriv y t) t) ∧ (∀ t, deriv x t = -2 * y t + u t) ∧ (∀ t, deriv y t = -2 * x t + u t) ∧ x T = 0 ∧ y T = 0) := sorry

theorem seq_convergence (x : ℕ → ℝ) (y : ℕ → ℝ) (hy : ∀ n ≥ 2, y n = x (n - 1) + 2 • x n) (L : ℝ) (hlim : Filter.Tendsto y Filter.atTop (nhds L)) : ∃ M : ℝ, Filter.Tendsto x Filter.atTop (nhds M) := sorry

theorem sum_divisors_divides_24 (n : ℕ) (h : (n + 1) ∣ 24) : (∑ d in Nat.divisors n, d) ∣ 24 := sorry

theorem three_subgroups_can_cover_finite_group : ∃ (G : Type*) [Group G] [Fintype G] (H K L : Subgroup G), Fintype.card (↥H) < Fintype.card G ∧ Fintype.card (↥K) < Fintype.card G ∧ Fintype.card (↥L) < Fintype.card G ∧ ↑H ∪ ↑K ∪ ↑L = (⊤ : Set G) := sorry

theorem sequence_limit_condition (T : ℕ → ℝ) (h_rec : ∀ n ≥ 1, T n * T (n + 1) = n) (h_lim : Tendsto (fun n => T n / T (n + 1)) atTop (𝓝 1)) : Real.pi * (T 1)^2 = 2 := sorry

theorem exists_rectangle_covering_curve (Γ : Set (ℝ × ℝ)) (hΓ : IsConnected Γ) (hl : arcLength Γ = 1) : ∃ (R : Set (ℝ × ℝ)), IsRectangle R ∧ IsClosed R ∧ Γ ⊆ R ∧ area R = 1/4 := sorry

theorem limit_of_count_ratio (a : ℕ → ℝ) (h_mono : StrictMono a) (h_sum : ∃ L : ℝ, Tendsto (fun n ↦ ∑ i in Finset.range n, (1 / a i)) atTop (𝓝 L)) (k : ℝ → ℕ) (hk : ∀ x, k x = Nat.card {n | a n ≤ x}) : Tendsto (fun x ↦ (k x : ℝ) / x) atTop (𝓝 0) := sorry

theorem matrix_mult_inverse {A : Matrix (Fin 3) (Fin 2) ℝ} {B : Matrix (Fin 2) (Fin 3) ℝ} (hAB : A * B = !![8, 2, -2; 2, 5, 4; -2, 4, 5]) : B * A = 9 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := sorry

theorem power_series_coefficients (a b : ℝ) (ha : a > 0) (hb : b > 0) : (∀ n, (PowerSeries.mk fun n => (a ^ n / Nat.factorial n) * Real.cos (b * ↑n)) n = 0) ∨ (Infinite {n | (PowerSeries.mk fun n => (a ^ n / Nat.factorial n) * Real.cos (b * ↑n)) n = 0}) := sorry

theorem nonvanishing_expression (A B C D E F G : ℝ) (h : B^2 - 4 * A * C < 0) : ∃ δ > 0, ∀ (x y : ℝ), 0 < x^2 + y^2 ∧ x^2 + y^2 < δ → A * x^2 + B * x * y + C * y^2 + D * x^3 + E * x^2 * y + F * x * y^2 + G * y^3 ≠ 0 := sorry

theorem smallest_square_with_three_equal_nonzero_trailing_digits : Nat.find (fun n => ∃ (d : Fin 10) (h : d ≠ 0), Nat.pow n 2 % 1000 = d * 111) = 38 ∧ Nat.pow 38 2 = 1444 := sorry

theorem seq_diff_converges (x : ℕ → ℝ) (h : Filter.Tendsto (fun n ↦ x n - x (n - 2)) Filter.atTop (nhds 0)) : Filter.Tendsto (fun n ↦ (x n - x (n - 1)) / ↑n) Filter.atTop (nhds 0) := sorry

theorem limit_expression (n : ℕ) : Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ) ^ 4) * (∏ i in Finset.range (2 * n + 1), (n^2 + i^2) ^ (1 / (n : ℝ)))) Filter.atTop (nhds (Real.exp (2 * Real.log 5 - 4 + 2 * Real.arctan 2))) := sorry

theorem polynomial_average_eq_endpoints (H : Polynomial ℝ) (hdeg : H.natDegree ≤ 3) (T : ℝ) (hT : T > 0) : (∫ t in -T..T, H t) / (2 * T) = (H (-T / Real.sqrt 3) + H (T / Real.sqrt 3)) / 2 := sorry

theorem projection_of_closed_set_is_closed {S : Set (ℝ × ℝ)} (hS : IsClosed S) {a b : ℝ} (hab : a < b) (h : ∀ (p : ℝ × ℝ), p ∈ S → a < p.1 ∧ p.1 < b) : IsClosed (Prod.snd '' S) := sorry

theorem exists_second_deriv_large (x : ℝ → ℝ) (hx : ContDiff ℝ 2 x) (hx0 : x 1 - x 0 = 1) (hx'0 : deriv x 0 = 0) (hx'1 : deriv x 1 = 0) (hx'bdd : ∀ t ∈ Icc 0 1, |deriv x t| ≤ 3/2) : ∃ t ∈ Icc 0 1, |deriv^[2] x t| ≥ 9/2 := sorry

theorem continuous_iff_compose_with_cutoff (F : ℝ → ℝ) : Continuous F ↔ ∀ (n : ℕ), Continuous (fun x ↦ if x ≤ -↑n then -↑n else if x ≤ ↑n then x else ↑n ∘ F) := sorry

theorem quadrilateral_inscribed_and_circumscribed {a b c d : ℝ} (h₁ : a > 0) (h₂ : b > 0) (h₃ : c > 0) (h₄ : d > 0) (h₅ : ∃ (quad : ConvexQuadrilateral ℝ), quad.side_lengths = (a, b, c, d) ∧ quad.area = Real.sqrt (a * b * c * d)) (h₆ : ∃ (C : Circle ℝ), TangentToAllSides C quad) : ∃ (C' : Circle ℝ), CircumscribedAbout quad C' := sorry

