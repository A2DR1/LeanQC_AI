
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


theorem product_of_nonzero_rational_and_irrational_is_irrational (r : ℚ) (hr : r ≠ 0) (x : ℝ) (hx : Irrational x) : Irrational (r * x) := sorry

theorem lower_bound_le_upper_bound (S : Type*) [Preorder S] (E : Set S) (hE_nonempty : E.Nonempty) (α β : ℝ) (hα_lower_bound : ∀ x ∈ E, α ≤ (x : ℝ)) (hβ_upper_bound : ∀ x ∈ E, (x : ℝ) ≤ β) : α ≤ β := sorry

theorem exists_complex_not_trichotomy : ∃ (a : ℂ), ¬ (∀ (a b c : ℂ), (a < b → a + c < b + c) ∧ (a < b ∧ 0 < c → a * c < b * c) ∧ (a < b ∨ a = b ∨ b < a)) := sorry

theorem triangle_inequality_sum (n : ℕ) (z : ℕ → ℂ) : 
    Complex.abs (∑ k in Finset.range n, z k) ≤ ∑ k in Finset.range n, Complex.abs (z k) := sorry

theorem complex_modulus_identity (z : ℂ) (hz : z * conj z = 1) : |1 + z| ^ 2 + |1 - z| ^ 2 = 4 := sorry

theorem parallelogram_law (k : ℕ) (x y : EuclideanSpace ℝ (Fin k)) : 
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := sorry

theorem not_product_zero (x : ℝ) (y : ℝ) (hy : y ≠ 0) : ¬(x * y = 0) := sorry

theorem separated_sets_of_disjoint_closed {X : Type _} [MetricSpace X] (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (hDisj : A ∩ B = ∅) : SeparatedNhds A B := sorry

theorem countable_base_of_compact_metric_space (K : Type*) [MetricSpace K] [CompactSpace K] : 
    ∃ (B : Set (Set K)), Set.Countable B ∧ TopologicalSpace.IsTopologicalBasis B := sorry

theorem condensation_points_countable_complement (k : ℕ) (E : Set (ℝ ^ k)) (hE : Set.Uncountable E) :
    Set.Countable {x ∈ E | x ∉ condensationPoints E} := sorry

theorem exists_disjoint_open_intervals_covering (U : Set ℝ) (hU_open : IsOpen U) (r : U → U → Prop) (hr_def : ∀ (x y : U), r x y ↔ Set.Icc (min (x : ℝ) (y : ℝ)) (max (x : ℝ) (y : ℝ)) ⊆ U) (hr_equiv : Equivalence r) : 
    ∃ (S : Set (Set ℝ)), (∀ I ∈ S, ∃ a b : ℝ, a < b ∧ I = Set.Ioo a b) ∧ 
    (∀ I J ∈ S, I ≠ J → Disjoint I J) ∧ 
    Set.Countable S ∧ ⋃₀ S = U := sorry

theorem limit_of_sqrt_n_sq_plus_n_minus_n : Filter.Tendsto (fun (n : ℕ) => Real.sqrt ((n : ℝ) ^ 2 + (n : ℝ)) - (n : ℝ)) Filter.atTop (𝓝 ((1 : ℝ) / 2)) := sorry

theorem limsup_sum_le_sum_limsup (a b : ℕ → ℝ) : 
    limsup (fun n => a n + b n) atTop ≤ limsup a atTop + limsup b atTop := sorry

theorem series_sqrt_div_converges (a : ℕ → ℝ) (ha_nonneg : ∀ n, 0 ≤ a n) (ha_converges : Summable a) : 
    Summable (λ n => Real.sqrt (a n) / (n : ℝ)) := sorry

theorem absolute_convergence_of_cauchy_product (a b : ℕ → ℝ) (ha : Summable fun n : ℕ => ‖a n‖) (hb : Summable fun n : ℕ => ‖b n‖) : 
    Summable fun n : ℕ => ‖∑ k in Finset.range (n + 1), a k * b (n - k)‖ := sorry

theorem nested_closed_sets_singleton_intersection (X : Type*) [MetricSpace X] [CompleteSpace X] (E : ℕ → Set X) 
    (h_closed : ∀ n, IsClosed (E n)) (h_nonempty : ∀ n, Set.Nonempty (E n)) (h_bounded : ∀ n, Bornology.IsBounded (E n))
    (h_nested : ∀ n, E n ⊇ E (n + 1)) (h_diam_tendsto_zero : Filter.Tendsto (λ n => Metric.diam (E n)) Filter.atTop (nhds 0)) : 
    Set.Subsingleton (⋂ n, E n) ∧ ∃ x, ⋂ n, E n = {x} := sorry

theorem exists_function_with_limit_zero_and_discontinuous : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Filter.Tendsto (λ (h : ℝ) => f (x + h) - f (x - h)) (𝓝 0) (𝓝 0)) ∧ ∃ (a : ℝ), ¬ ContinuousAt f a := sorry

theorem closed_zero_set_of_continuous_function {X : Type _} [MetricSpace X] (f : X → ℝ) (hf : Continuous f) : IsClosed {p : X | f p = 0} := sorry

theorem dense_subset_continuous_functions_equal (X Y : Type) [MetricSpace X] [MetricSpace Y] (E : Set X) (hE_dense : Dense E) (f g : X → Y) (hf_cont : Continuous f) (hg_cont : Continuous g) (h_eq_on_E : ∀ p ∈ E, f p = g p) : ∀ p : X, f p = g p := sorry

theorem exists_set_and_function_with_distinct_continuous_extension : ∃ (E : Set ℝ) (f : E → ℝ), ContinuousOn f E ∧ ∀ (g : ℝ → ℝ), Continuous g → ∃ x ∈ E, g x ≠ f x := sorry

theorem exists_bound_on_bounded_set (E : Set ℝ) (hE : Metric.Bounded E) (f : ℝ → ℝ) 
    (hf : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ E, ∀ y ∈ E, |x - y| < δ → |f x - f y| < ε) : 
    ∃ M > 0, ∀ x ∈ E, |f x| < M := sorry

theorem uniform_continuity_preserves_cauchy_sequences {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] (f : X → Y) (hf : ∀ ε > 0, ∃ δ > 0, ∀ (a b : X), dist a b < δ → dist (f a) (f b) < ε) (seq : ℕ → X) (hseq : ∀ ε > 0, ∃ N : ℕ, ∀ (m n : ℕ), m > N → n > N → dist (seq m) (seq n) < ε) : ∀ ε > 0, ∃ N : ℕ, ∀ (m n : ℕ), m > N → n > N → dist (f (seq m)) (f (seq n)) < ε := sorry

theorem monotonic_or_antimonotonic (f : ℝ → ℝ) (hcont : ∀ x, ContinuousAt f x) (hopen : ∀ x, IsOpenMap f) : 
    (∀ a b, a < b → f a ≤ f b) ∨ (∀ a b, a < b → f a ≥ f b) := sorry

theorem exists_positive_distance_between_compact_and_closed (X : Type*) [MetricSpace X] (K F : Set X) (hK : IsCompact K) (hF : IsClosed F) (h_disjoint : ∀ p ∈ K, ∀ q ∈ F, p ≠ q) : ∃ δ > 0, ∀ p ∈ K, ∀ q ∈ F, dist p q > δ := sorry

theorem exists_constant_function : ∃ (c : ℝ), ∀ (x : ℝ), f x = c := sorry

theorem exists_delta_for_injective : ∃ (δ : ℝ), δ > 0 ∧ ∀ (ε : ℝ), ε > 0 → ε < δ → ∀ (g : ℝ → ℝ), (∀ x, DifferentiableAt ℝ g x) → (∀ x, ‖deriv g x‖ ≤ M) → (M > 0) → ∀ (f : ℝ → ℝ), (∀ x, f x = x + ε * g x) → ∀ (a b : ℝ), f a = f b → a = b := sorry

theorem limit_of_difference : ∀ ε > 0, ∃ N > 0, ∀ x > N, |(fun (x : ℝ) => f (x + 1) - f x) x| < ε := sorry

theorem lhopital_limit : 
    ∀ (f g : ℝ → ℝ) (x : ℝ), 
    (∀ t : ℝ, DifferentiableAt ℝ f t) → 
    (∀ t : ℝ, DifferentiableAt ℝ g t) → 
    deriv g x ≠ 0 → 
    f x = 0 → 
    g x = 0 → 
    Tendsto (λ t => f t / g t) (𝓝 x) (𝓝 (deriv f x / deriv g x)) := sorry

theorem exists_third_derivative_ge_three : ∃ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 ∧ f''' x ≥ 3 := sorry

theorem exists_set_not_topology : ∃ (X : Set ℕ), ¬ IsTopologicalSpace X (λ (U : Set X) => (Set.Infinite (X \ U)) ∨ (X \ U = (∅ : Set X)) ∨ (X \ U = X)) := sorry

theorem exists_set_and_topologies_where_union_not_topology : ∃ (X : Type) (I : Type) (T : I → TopologicalSpace X), ¬ IsTopology (⋃ α : I, {T α}) := sorry

theorem exists_coarsest_topology (X : Type*) (I : Type*) (𝒯_α : I → TopologicalSpace X) : 
    ∃ (𝒯 : TopologicalSpace X), (∀ α, 𝒯 ≤ 𝒯_α α) ∧ ∀ (𝒮 : TopologicalSpace X), (∀ α, 𝒮 ≤ 𝒯_α α) → 𝒮 ≤ 𝒯 := sorry

theorem topology_generated_eq_intersection (X : Type*) (𝒜 : Set (Set X)) (h : IsTopologicalBasis 𝒜) :
    let τ_g := TopologicalSpace.generateFrom 𝒜
    let T := {τ : TopologicalSpace X | 𝒜 ⊆ {s | IsOpen[τ] s}}
    let τ_i := ⨅ τ ∈ T, τ
    τ_g = τ_i := sorry

theorem topology_equality : 
    (let T : Set (Set ℝ) := {U | ∀ x ∈ U, ∃ ε > (0 : ℝ), Set.Ioo (x - ε) (x + ε) ⊆ U} in
    let B : Set (Set ℝ) := {I | ∃ (a b : ℚ), a < b ∧ I = Set.Ioo (a : ℝ) (b : ℝ)} in
    let T_B : Set (Set ℝ) := {U | ∀ x ∈ U, ∃ I ∈ B, x ∈ I ∧ I ⊆ U} in
    T = T_B) := sorry

theorem subspace_topology_equality (X : Type*) [TopologicalSpace X] (Y : Set X) [TopologicalSpace Y] (A : Set Y) :
    ∀ (W : Set A), IsOpen[Subtype.topologicalSpace] W ↔ IsOpen[instTopologicalSpaceSubtype] W := sorry

theorem basis_for_standard_topology_on_R2 : TopologicalSpace.IsTopologicalBasis (Set.range fun (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ) (ha : a < b) (hc : c < d) => {p : ℝ × ℝ | (a : ℝ) < p.1 ∧ p.1 < (b : ℝ) ∧ (c : ℝ) < p.2 ∧ p.2 < (d : ℝ)}) := sorry

theorem closed_set_of_le {X : Type*} [TopologicalSpace X] {Y : Type*} [LinearOrder Y] [TopologicalSpace Y] [OrderTopology Y] {f g : X → Y} (hf : Continuous f) (hg : Continuous g) : IsClosed {x : X | f x ≤ g x} := sorry

theorem continuous_extension_unique (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] (A : Set X) (f : A → Y) (hf : Continuous f) (g : closure A → Y) (hg : Continuous g) (hgf : ∀ a : A, g (Subtype.mk a.1 (subset_closure a.2)) = f a) : ∀ (h : closure A → Y) (hh : Continuous h) (hhf : ∀ a : A, h (Subtype.mk a.1 (subset_closure a.2)) = f a), ∀ x : closure A, h x = g x := sorry

theorem exists_metric_induces_dictionary_order_topology : ∃ (d : (ℝ × ℝ) → (ℝ × ℝ) → ℝ), MetricSpace.mk d (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance) ∧ TopologicalSpace.IsTopologicalBasis (Metric.ball (x := (0,0)) (r := 1)) = TopologicalSpace.generateFrom {s | ∃ (a b : ℝ × ℝ), s = Set.Ioo a b} := sorry

theorem exists_epsilon_gt_zero_for_all_N_exists_m_ge_N_and_x_in_01_such_that_abs_diff_ge_epsilon : ∃ ε : ℝ, ε > 0 ∧ ∀ N : ℕ, ∃ m : ℕ, m ≥ N ∧ ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ |(x ^ m) - (if x = 1 then (1 : ℝ) else (0 : ℝ))| ≥ ε := sorry

theorem quotient_map_of_continuous_right_inverse (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (f : Y → X) (hp : Continuous p) (hf : Continuous f) (h : ∀ y, p (f y) = y) : QuotientMap p := sorry

theorem open_map_restriction_to_image (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hp : IsOpenMap p) (A : Set X) (hA : IsOpen A) : IsOpenMap (fun (x : A) => ⟨p x.val, by
    have : x.val ∈ A := x.property
    exact Set.mem_image_of_mem p this⟩ : A → p '' A) := sorry

theorem union_of_connected_with_nonempty_intersection_is_connected (X : Type*) [TopologicalSpace X] 
    (A : Set X) (hA_conn : IsConnected A) (𝒜 : Set (Set X)) (h𝒜_conn : ∀ B ∈ 𝒜, IsConnected B) 
    (h_nonempty_inter : ∀ B ∈ 𝒜, (A ∩ B).Nonempty) : IsConnected (A ∪ ⋃₀ 𝒜) := sorry

theorem exists_point_in_boundary_of_subset (X : Type) [TopologicalSpace X] (A C : Set X) (hC : IsConnected C) (hp : ∃ p, p ∈ C ∧ p ∈ A) (hq : ∃ q, q ∈ C ∧ q ∈ (X \ A)) : ∃ r, r ∈ C ∧ r ∈ frontier A := sorry

theorem connected_of_quotient_map_with_connected_fibers {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hp : QuotientMap p) (hfibers : ∀ y : Y, IsConnected (p⁻¹' {y})) (hY : IsConnected (Set.univ : Set Y)) : IsConnected (Set.univ : Set X) := sorry

theorem exists_fixed_point : ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ f x = x := sorry

theorem connected_component_of_identity_is_normal_subgroup (G : Type*) [TopologicalSpace G] [Group G] [TopologicalGroup G] :
    let C := connectedComponent (e : G) in
    Subgroup.Normal (Subgroup.closure (C : Set G)) := sorry

theorem compact_of_closed_continuous_surjective_preimage_compact {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (h_closed : IsClosedMap p) (h_cont : Continuous p) (h_surj : Function.Surjective p) (h_preimage_compact : ∀ y : Y, IsCompact (p ⁻¹' {y})) (hY_compact : IsCompact (Set.univ : Set Y)) : IsCompact (Set.univ : Set X) := sorry

theorem countably_compact_iff_limit_point_compact (X : Type*) [TopologicalSpace X] [T1Space X] :
    (∀ (U : ℕ → Set X), (∀ n, IsOpen (U n)) → (⋃ n, U n = ⊤) → ∃ (F : Finset ℕ), ⋃ n ∈ F, U n = ⊤) ↔
    (∀ (A : Set X), Set.Infinite A → ∃ (x : X), ClusterPt x (Filter.principal A)) := sorry

theorem metric_fixed_point_bijective_homeomorphism (X : Type*) [TopologicalSpace X] [CompactSpace X] (d : X → X → ℝ) (f : X → X) (h_nonneg : ∀ x y, 0 ≤ d x y) (h_eq_zero_iff : ∀ x y, d x y = 0 ↔ x = y) (h_symm : ∀ x y, d x y = d y x) (h_triangle : ∀ x y z, d x z ≤ d x y + d y z) (h_isometry : ∀ x y, d (f x) (f y) = d x y) : Function.Bijective f ∧ Homeomorph X X := sorry

theorem exists_point_with_noncompact_closure : ∃ (x : ℕ → Set.Icc (0 : ℝ) 1), ∀ (U : Set (ℕ → Set.Icc (0 : ℝ) 1)), IsOpen U → x ∈ U → ¬IsCompact (closure U) := sorry

theorem countable_dense_in_product {I : Type*} [Countable I] (X : I → Type*) [∀ i, TopologicalSpace (X i)]
    (h : ∀ i, ∃ (D : Set (X i)), Countable D ∧ Dense D) :
    ∃ (D : Set (∀ i, X i)), Countable D ∧ Dense D := sorry

theorem exists_disjoint_open_sets_of_distinct_points_in_regular_space {X : Type _} [TopologicalSpace X] [RegularSpace X] (x y : X) (h : x ≠ y) : ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ closure U ∩ closure V = ∅ := sorry

theorem order_topology_is_regular (X : Type*) [TopologicalSpace X] (h : IsOrderTopology X) : RegularSpace X := sorry

theorem product_hausdorff_implies_factor_hausdorff {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] (h_nonempty : ∀ i, Nonempty (X i)) (h_product : T2Space (∀ i, X i)) : ∀ i, T2Space (X i) := sorry

theorem product_normal_implies_factor_normal {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, Nonempty (X i)] (h : NormalSpace (∀ i, X i)) : ∀ i, NormalSpace (X i) := sorry

theorem exists_continuous_function_separating_point_from_closed {X : Type _} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] (x : X) (F : Set X) (hF : IsClosed F) (hxF : x ∉ F) : ∃ f : C(X, ℝ), f x = 0 ∧ ∀ y ∈ F, f y = 1 := sorry

theorem metrizable_of_compact_Hausdorff_union_of_closed_metrizable_subspaces
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (X₁ X₂ : Set X) (hX₁_closed : IsClosed X₁) (hX₂_closed : IsClosed X₂)
    (hX_union : X₁ ∪ X₂ = Set.univ)
    (hX₁_metrizable : MetrizableSpace (Subtype X₁))
    (hX₂_metrizable : MetrizableSpace (Subtype X₂)) :
    MetrizableSpace X := sorry

theorem exists_unique_continuous_extension (X : Type) (Y : Type) (d_X : X → X → ℝ) (d_Y : Y → Y → ℝ) (A : Set X) (f : A → Y) (hX_metric : ∀ (x₁ x₂ : X), d_X x₁ x₂ ≥ 0) (hX_zero : ∀ (x₁ x₂ : X), d_X x₁ x₂ = 0 ↔ x₁ = x₂) (hX_symm : ∀ (x₁ x₂ : X), d_X x₁ x₂ = d_X x₂ x₁) (hX_triangle : ∀ (x₁ x₂ x₃ : X), d_X x₁ x₃ ≤ d_X x₁ x₂ + d_X x₂ x₃) (hY_metric : ∀ (y₁ y₂ : Y), d_Y y₁ y₂ ≥ 0) (hY_zero : ∀ (y₁ y₂ : Y), d_Y y₁ y₂ = 0 ↔ y₁ = y₂) (hY_symm : ∀ (y₁ y₂ : Y), d_Y y₁ y₂ = d_Y y₂ y₁) (hY_triangle : ∀ (y₁ y₂ y₃ : Y), d_Y y₁ y₃ ≤ d_Y y₁ y₂ + d_Y y₂ y₃) (hY_complete : CompleteSpace Y) (hf_uniform : ∀ ε > 0, ∃ δ > 0, ∀ (a₁ a₂ : A), d_X a₁.val a₂.val < δ → d_Y (f a₁) (f a₂) < ε) : ∃! (g : closure A → Y), (∀ (a : A) (ha : a.val ∈ closure A), g ⟨a.val, ha⟩ = f a) ∧ (∀ ε > 0, ∃ δ > 0, ∀ (x₁ x₂ : closure A), d_X x₁.val x₂.val < δ → d_Y (g x₁) (g x₂) < ε) := sorry

theorem ω_cube_eq_one : ω ^ 3 = 1 := sorry

theorem zero_product_in_vector_space (F : Type _) [Field F] (V : Type _) [AddCommGroup V] [Module F V] (a : F) (v : V) (h : a • v = 0) : a = 0 ∨ v = 0 := sorry

theorem exists_subset_not_subspace : ∃ (U : Set (ℝ × ℝ)), U.Nonempty ∧ (∀ (λ : ℝ) (v : ℝ × ℝ), v ∈ U → (λ • v) ∈ U) ∧ ¬ (Submodule ℝ (ℝ × ℝ)).carrier U := sorry

theorem subspace_union_iff_subspace_subset (F : Type*) [Field F] (V : Type*) [AddCommGroup V] [Module F V] (U W : Submodule F V) :
    (Submodule F V).IsSubmodule (U.carrier ∪ W.carrier) ↔ (U ≤ W ∨ W ≤ U) := sorry

theorem exists_subspace_with_trivial_intersection_and_range (V W : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] (T : V →ₗ[ℝ] W) : ∃ (U : Submodule ℝ V), (U ⊓ LinearMap.ker T = ⊥) ∧ (LinearMap.range T = T '' U) := sorry

theorem linear_operator_preserves_sum_of_invariant_subspaces {V : Type _} [AddCommMonoid V] [Module ℝ V] (T : V →ₗ[ℝ] V) (m : ℕ) (U : Fin m → Submodule ℝ V) (h_invariant : ∀ (i : Fin m) (u : V), u ∈ U i → T u ∈ U i) : 
    ∀ (w : V), w ∈ ∑ i : Fin m, U i → T w ∈ ∑ i : Fin m, U i := sorry

theorem eigenvalue_composition (F : Type _) [Field F] (V : Type _) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (S T : V →ₗ[F] V) (λ : F) (h : λ ∈ Module.End.eigenvalues (S ∘ₗ T)) : λ ∈ Module.End.eigenvalues (T ∘ₗ S) := sorry

theorem exists_scalar_for_linear_operator (F : Type*) [Field F] (V : Type*) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (T : V →ₗ[F] V) 
    (h : ∀ (U : Submodule F V), FiniteDimensional.finrank F U = FiniteDimensional.finrank F V - 1 → Submodule.map T U ≤ U) : 
    ∃ (λ : F), ∀ (v : V), T v = λ • v := sorry

theorem subspace_dim_even (V : Type _) [AddCommGroup V] [Module ℝ V] (T : V →ₗ[ℝ] V) (hT : ∀ (λ : ℝ) (v : V), v ≠ 0 → T v ≠ λ • v) (U : Submodule ℝ V) (hU : ∀ u : V, u ∈ U → T u ∈ U) : ∃ (k : ℕ), Module.rank ℝ U = 2 * k := sorry

theorem cauchy_schwarz_weighted_sum (n : ℕ) (a b : ℕ → ℝ) :
    (∑ j in Finset.Icc 1 n, a j * b j) ^ 2 ≤ (∑ j in Finset.Icc 1 n, j * (a j) ^ 2) * (∑ j in Finset.Icc 1 n, (b j) ^ 2 / j) := sorry

theorem orthonormal_span_iff (m : ℕ) (V : Type _) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (e : Fin m → V) (h_orthonormal : ∀ i j : Fin m, ⟪e i, e j⟫_ℝ = if i = j then (1 : ℝ) else (0 : ℝ)) (v : V) :
    (‖v‖ ^ 2 = ∑ i : Fin m, |⟪v, e i⟫_ℝ| ^ 2) ↔ v ∈ Submodule.span ℝ (Set.range e) := sorry

theorem exists_normal_operators_with_non_normal_sum : 
    ∃ (V : Type) [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (h_dim : FiniteDimensional.finrank ℂ V ≥ 2) 
    (A B : V →ₗ[ℂ] V) (_ : A.IsNormal) (_ : B.IsNormal), ¬ (A + B).IsNormal := sorry

theorem self_adjoint_iff_eigenvalues_real (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (T : V →ₗ[ℂ] V) (hT_normal : LinearMap.IsNormal T) :
    (∀ (v : V) (λ : ℂ), v ≠ 0 → T v = λ • v → λ ∈ Set.range ((algebraMap ℝ ℂ) : ℝ → ℂ)) ↔ LinearMap.IsSelfAdjoint T := sorry

theorem exists_square_root_of_normal_operator (V : Type _) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (T : V →L[ℂ] V) (hT : IsNormal T) : ∃ (S : V →L[ℂ] V), S ^ 2 = T := sorry

theorem sum_reciprocals_not_integer (n : ℕ) (hn : n ≥ 2) : ¬ (∑ i in Finset.Icc 2 n, (1 : ℚ) / i).den = 1 := sorry

theorem gcd_of_power_of_two_plus_one (a : ℤ) (hm : a ≠ 0) (m n : ℕ) (hn : n > m) : 
    let d := (a ^ (2 ^ n) + 1).gcd (a ^ (2 ^ m) + 1) in
    (Odd a → d = 1) ∧ (Even a → d = 2) := sorry

theorem limit_of_partial_sums_diverges : Filter.Tendsto (λ N : ℕ ↦ ∑ n in Finset.range (N + 1), (if Squarefree n then (1 : ℕ) else 0) / (n + 1)) Filter.atTop Filter.atTop := sorry

theorem no_square_eq_three_x_sq_plus_two (x y : ℤ) : ¬(3 * (x ^ 2) + 2 = y ^ 2) := sorry

theorem exists_int_k_for_factorial (n : ℕ) (hn_not_prime : ¬ Nat.Prime n) (hn_ne_four : n ≠ 4) : ∃ (k : ℤ), ((n - 1)! : ℤ) = (n : ℤ) * k := sorry

theorem primitive_root_neg (t : ℕ) (p : ℕ) (hp : p = 4 * t + 1) (hprime : Nat.Prime p) (a : ℤ) (hprim : IsPrimitiveRoot a p) : IsPrimitiveRoot (-a) p := sorry

theorem fermat_prime_primitive_root_three (n : ℕ) (hp : Nat.Prime ((2 : ℕ) ^ n + 1)) (hfermat : FermatPrime ((2 : ℕ) ^ n + 1)) : IsPrimitiveRoot (3 : ℤ) ((2 : ℕ) ^ n + 1) := sorry

theorem sum_of_powers_mod_p (p : ℕ) (hp : Nat.Prime p) (hpgt : p > 2) (k : ℕ) :
    let A := Finset.Ico 1 p
    let S := ∑ a in A, a ^ k
    in if ¬ (p - 1) ∣ k then S % p = 0 else S % p = p - 1 := sorry

theorem exists_A_B_iff_exists_x (hp : Nat.Prime p) (hp_mod : p % 4 = 1) : 
    (∃ (A B : ℤ), (p : ℤ) = A ^ 2 + 64 * B ^ 2) ↔ 
    (∃ (x : ℤ) (hx : x ∈ {x | (0 : ℤ) ≤ x ∧ x < p}), ((x ^ 4) % p : ℤ) = 2) := sorry

theorem exists_polynomial_with_integer_coefficients : ∃ (P : Polynomial ℤ), Polynomial.eval (Real.sin (π / 12)) (Polynomial.map (Int.castRingHom ℝ) P) = 0 := sorry

theorem constant_on_connected_open_subset_of_constant_imaginary_part (Ω : Set ℂ) (hΩ_open : IsOpen Ω) (hΩ_conn : IsConnected Ω) (f : ℂ → ℂ) (hf_holomorphic : DifferentiableOn ℂ f Ω) (C : ℝ) (h_const_imag : ∀ z ∈ Ω, Complex.im (f z) = C) : ∃ z₀ ∈ Ω, ∀ z ∈ Ω, f z = f z₀ := sorry

theorem series_diverges_on_unit_circle : ∀ z : ℂ, Complex.abs z = 1 → ¬ Summable (λ n : ℕ => (n : ℂ) * z ^ n) := sorry

theorem series_convergence_for_unit_circle (z : ℂ) (hz_abs : Complex.abs z = 1) (hz_ne_one : z ≠ 1) : 
    Summable fun n : ℕ => z ^ (n + 1) / ((n : ℂ) + 1) := sorry

theorem integral_sin_div_x_eq_pi_div_two : ∫ x in Set.Ioi (0 : ℝ), (Real.sin x) / x = π / 2 := by
  let I : ℝ → ℝ := fun t => ∫ x in Set.Ioi (0 : ℝ), (Real.exp (-t * x)) * (Real.sin x) / x
  have h_converges : ∀ t > 0, Integrable (fun x : ℝ => (Real.exp (-t * x)) * (Real.sin x) / x) (Measure.restrict volume (Set.Ioi (0 : ℝ))) := sorry
  have h_deriv_eq : ∀ t > 0, HasDerivAt I (-∫ x in Set.Ioi (0 : ℝ), (Real.exp (-t * x)) * Real.sin x) t := sorry
  have h_integral_eq : ∀ t > 0, ∫ x in Set.Ioi (0 : ℝ), (Real.exp (-t * x)) * Real.sin x = 1 / (1 + t ^ 2) := sorry
  have h_deriv_simp : ∀ t > 0, HasDerivAt I (-(1 / (1 + t ^ 2))) t := sorry
  have h_form : ∀ t > 0, ∃ C : ℝ, I t = C - Real.arctan t := sorry
  have h_limit : Filter.Tendsto I Filter.atTop (𝓝 0) := sorry
  have h_const : ∃ C : ℝ, ∀ t > 0, I t = C - Real.arctan t := sorry
  rcases h_const with ⟨C, hC⟩
  have h_limit_const : Filter.Tendsto (fun t : ℝ => C - Real.arctan t) Filter.atTop (𝓝 0) := by
    simpa [hC] using h_limit
  have hC_zero : C = π / 2 := sorry
  have h_zero_pos : I 0 = ∫ x in Set.Ioi (0 : ℝ), (Real.sin x) / x := by
    simp [I]
  calc
    ∫ x in Set.Ioi (0 : ℝ), (Real.sin x) / x = I 0 := by symm; exact h_zero_pos
    _ = C - Real.arctan 0 := hC 0 (by norm_num)
    _ = π / 2 - 0 := by rw [hC_zero, Real.arctan_zero]
    _ = π / 2 := by ring
    := sorry

theorem analytic_function_with_locally_zero_coefficients_is_polynomial (f : ℂ → ℂ) (hf : AnalyticOn ℂ f Set.univ) 
    (h : ∀ (z₀ : ℂ), ∃ (n : ℕ), (Complex.hasFPowerSeriesOnBall_iff.mp (hf z₀ (Set.mem_univ z₀))).1.coeff n = 0) : 
    ∃ (p : Polynomial ℂ), ∀ (z : ℂ), f z = Polynomial.eval z p := sorry

theorem integral_of_x_sin_over_x_sq_plus_a_sq (a : ℝ) (ha : a > 0) : 
    ∫ (x : ℝ), (x * Real.sin x) / (x ^ 2 + a ^ 2) = π * Real.exp (-a) := sorry

theorem entire_injective_is_affine : ∃ (a b : ℂ), a ≠ 0 ∧ ∀ (z : ℂ), f z = a * z + b := sorry

theorem sum_one_minus_abs_z_n_converges : 
    ∃ (M : ℝ), ∀ (f : ℂ → ℂ) (h_holo : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1)) 
    (h_bdd : ∃ (M : ℝ), ∀ z, ‖z‖ < 1 → ‖f z‖ ≤ M) (h_nonzero : ¬∀ z, ‖z‖ < 1 → f z = 0) 
    (z_seq : ℕ → ℂ) (h_in_ball : ∀ n, ‖z_seq n‖ < 1) (h_zero : ∀ n, f (z_seq n) = 0) 
    (h_all_zeros : ∀ z, ‖z‖ < 1 → f z = 0 → ∃ n, z = z_seq n), 
    Summable (λ n => 1 - ‖z_seq n‖) := sorry

theorem exists_derivative_negative : ∃ (n : ℕ) (x : ℝ), iteratedDeriv n f x < 0 := sorry

theorem exists_periodic_sequence (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1) (hx1 : x 1 = a) (hx2 : x 2 = a) (hrec : ∀ n ≥ 2, x (n + 1) = 2 * x n * x (n - 1) - x (n - 2)) (hzero : ∃ n, x n = 0) : ∃ p > 0, ∀ k, x (k + p) = x k := sorry

theorem incomplete_statement : False := sorry

theorem exists_unique_pair_of_positive_integers_satisfying_equation : ∃! (a n : ℕ), a > 0 ∧ n > 0 ∧ a ^ (n + 1) - (a + 1) ^ n = 2001 := sorry

theorem derivative_bound : ∀ (f : ℝ → ℝ), (∀ x, DifferentiableAt ℝ f x) → (∀ x, f x > 0) → (∀ x, deriv f x > 0) → (∀ x, deriv (deriv f) x > 0) → (∀ x, deriv (deriv (deriv f)) x > 0) → (∀ x, deriv (deriv (deriv f)) x ≤ f x) → ∀ x, deriv f x < 2 * f x := sorry

theorem exists_noninteger_sqrt (a b c : ℤ) : ∃ n : ℕ, 0 < n ∧ ¬ (Int.sqrt (n^3 + a * (n^2 : ℤ) + b * n + c)).1 = (Int.sqrt (n^3 + a * (n^2 : ℤ) + b * n + c)).1 := sorry

theorem open_iff_not_limit_point_of_complement (M : Type*) [MetricSpace M] (U : Set M) : 
    IsOpen U ↔ ∀ x ∈ U, ¬ IsLimitPoint x (M \ U) := sorry

theorem discrete_metric_open_subset (S : Set ℕ) : 
    (∀ x ∈ S, ∃ (r : ℝ), r > 0 ∧ ∀ (y : ℕ), (if x ≠ y then (1 : ℝ) else 0) < r → y ∈ S) ∧ 
    (∀ x ∉ S, ∃ (r : ℝ), r > 0 ∧ ∀ (y : ℕ), (if x ≠ y then (1 : ℝ) else 0) < r → y ∉ S) := sorry

theorem exists_min_distance_between_compact_sets (M : Type*) [MetricSpace M] (A B : Set M) (hA_compact : IsCompact A) (hB_compact : IsCompact B) (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty) (h_disjoint : ∀ a ∈ A, ∀ b ∈ B, a ≠ b) : ∃ a0 ∈ A, ∃ b0 ∈ B, ∀ a ∈ A, ∀ b ∈ B, dist a0 b0 ≤ dist a b := sorry

