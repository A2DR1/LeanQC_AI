
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


theorem rational_mul_irrational_irrational (r : ℚ) (hr : r ≠ 0) (x : ℝ) (hx : Irrational x) : Irrational (r * x) := sorry

theorem lower_bound_le_upper_bound {α : Type _} [Preorder α] (E : Set α) (hE : E.Nonempty) (α_lb : α) (β_ub : α) (hα : α_lb ∈ lowerBounds E) (hβ : β_ub ∈ upperBounds E) : α_lb ≤ β_ub := sorry

theorem no_order_on_complex : ¬∃ (order : ℂ → ℂ → Prop) [IsOrder ℂ order], IsOrderedField ℂ order := sorry

theorem complex_abs_sum_inequality (n : ℕ) (z : Fin n → ℂ) : 
    Complex.abs (∑ i : Fin n, z i) ≤ ∑ i : Fin n, Complex.abs (z i) := sorry

theorem compute_sum_of_squares (z : ℂ) (hz : Complex.normSq z = 1) : Complex.normSq (1 + z) + Complex.normSq (1 - z) = 4 := sorry

theorem parallelogram_law (k : ℕ) (x y : EuclideanSpace ℝ (Fin k)) : ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := sorry

theorem no_nonzero_orthogonal_when_k_one (x : ℝ) : ¬∃ (y : ℝ), y ≠ 0 ∧ x * y = 0 := sorry

theorem separated_of_disjoint_closed {X : Type*} [MetricSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hDisj : Disjoint A B) : SeparatedNhds A B := sorry

theorem countable_base_of_compact_metric_space (K : Type*) [MetricSpace K] [CompactSpace K] : ∃ (B : Set (Set K)), Set.Countable B ∧ TopologicalSpace.IsTopologicalBasis B := sorry

theorem condensation_points_countable (E : Set (ℝ ^ k)) (hE : Set.Uncountable E) : 
    Set.Countable (E \ {x | IsCondensationPoint x E}) := sorry

theorem open_set_is_countable_union_of_disjoint_segments : 
    ∀ (U : Set ℝ), IsOpen U → ∃ (S : Set (Set ℝ)), (∀ s ∈ S, ∃ a b : ℝ, a < b ∧ s = Set.Ioo a b) ∧ 
    (∀ s t ∈ S, s ≠ t → Disjoint s t) ∧ Set.Countable S ∧ U = ⋃₀ S := sorry

theorem limit_sqrt_n_sq_plus_n_minus_n : Filter.Tendsto (λ n : ℕ => Real.sqrt ((n : ℝ) ^ 2 + (n : ℝ)) - (n : ℝ)) Filter.atTop (𝓝 (1/2 : ℝ)) := sorry

theorem limsup_add_le_limsup_add_limsup (a b : ℕ → ℝ) (h : ¬ (limsup (a : ℕ → ℝ) atTop = ⊤ ∧ limsup (b : ℕ → ℝ) atTop = ⊥) ∧ ¬ (limsup (a : ℕ → ℝ) atTop = ⊥ ∧ limsup (b : ℕ → ℝ) atTop = ⊤)) : limsup (fun n => a n + b n) atTop ≤ limsup a atTop + limsup b atTop := sorry

theorem sum_convergence_implies_sqrt_over_n_convergence (a : ℕ → ℝ) (ha_nonneg : ∀ n, 0 ≤ a n) (h_converges : Summable a) : Summable (λ n => Real.sqrt (a n) / n) := sorry

theorem cauchy_product_abs_converges_abs (a b : ℕ → ℝ) (ha : Summable fun n => |a n|) (hb : Summable fun n => |b n|) :
    Summable fun n => |∑ k in Finset.range (n + 1), a k * b (n - k)| := sorry

theorem nested_closed_bounded_sets_intersection_singleton {X : Type*} [MetricSpace X] [CompleteSpace X] (E : ℕ → Set X) (h_closed : ∀ n, IsClosed (E n)) (h_nonempty : ∀ n, Set.Nonempty (E n)) (h_bounded : ∀ n, Bornology.IsBounded (E n)) (h_nested : ∀ n, E n ⊇ E (n + 1)) (h_diam_tendsto_zero : Filter.Tendsto (fun n => Metric.diam (E n)) Filter.atTop (nhds 0)) : ∃ x : X, ⋂ n, E n = {x} := sorry

theorem not_continuous_of_limit_zero : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Filter.Tendsto (λ h => f (x + h) - f (x - h)) (𝓝 0) (𝓝 0)) ∧ ¬ (∀ (x : ℝ), ContinuousAt f x) := sorry

theorem zero_set_of_continuous_function_is_closed {X : Type*} [MetricSpace X] (f : X → ℝ) (hf : Continuous f) : IsClosed {p : X | f p = 0} := sorry

theorem dense_subset_continuous_extension {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f g : X → Y} (hf : Continuous f) (hg : Continuous g) {E : Set X} (hE : Dense E) (h_eq_on_E : ∀ p ∈ E, g p = f p) : ∀ p : X, g p = f p := sorry

theorem exists_set_and_continuous_function_without_continuous_extension : ∃ (E : Set ℝ) (f : E → ℝ), Continuous f ∧ ¬∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x : E, g (x : ℝ) = f x := sorry

theorem uniform_continuous_on_bounded_set_implies_bounded {E : Set ℝ} (hE : Bornology.IsBounded E) (f : ℝ → ℝ) (hf : UniformContinuousOn f E) : Bounded (f '' E) := sorry

theorem uniform_continuous_preserves_cauchy_sequences {X : Type _} [MetricSpace X] {Y : Type _} [MetricSpace Y] (f : X → Y) (hf : UniformContinuous f) : ∀ (seq : ℕ → X), CauchySeq seq → CauchySeq (f ∘ seq) := sorry

theorem continuous_open_mapping_is_monotonic : ∀ (f : ℝ → ℝ), (Continuous f) → (∀ (U : Set ℝ), IsOpen U → IsOpen (f '' U)) → (∀ (x y : ℝ), x ≤ y → f x ≤ f y) ∨ (∀ (x y : ℝ), x ≤ y → f y ≤ f x) := sorry

theorem exists_positive_distance_between_compact_and_closed_disjoint_sets {X : Type*} [MetricSpace X] {K F : Set X} (hK : IsCompact K) (hF : IsClosed F) (hDisjoint : Disjoint K F) : ∃ δ > 0, ∀ p ∈ K, ∀ q ∈ F, δ < dist p q := sorry

theorem constant_function : ∀ (f : ℝ → ℝ), (∀ (x y : ℝ), |f x - f y| ≤ (x - y) ^ 2) → ∃ (c : ℝ), ∀ (x : ℝ), f x = c := sorry

theorem one_to_one_for_small_epsilon (g : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M) (hderiv : ∀ x, HasDerivAt g (g' x) x) (hbounded : ∀ x, |g' x| ≤ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ ε' < δ, Function.Injective (λ x => x + ε' * g x) := sorry

theorem limit_of_difference_quotient (f : ℝ → ℝ) (hderiv : ∀ x > 0, DifferentiableAt ℝ f x) (hlim : Tendsto (fderiv ℝ f) atTop (𝓝 0)) :
    Tendsto (λ x => f (x + 1) - f x) atTop (𝓝 0) := sorry

theorem limit_ratio_derivatives (f g : ℝ → ℝ) (x : ℝ) (hderiv_f : DifferentiableAt ℝ f x) (hderiv_g : DifferentiableAt ℝ g x) (hg'_nonzero : deriv g x ≠ 0) (hzero : f x = 0 ∧ g x = 0) : 
    Tendsto (λ t => f t / g t) (𝓝[≠] x) (𝓝 (deriv f x / deriv g x)) := sorry

theorem exists_third_derivative_ge_three : ∃ (f : ℝ → ℝ) (hf : DifferentiableOn ℝ f (Set.Icc (-1 : ℝ) 1)), 
    f (-1) = 0 ∧ f (0) = 0 ∧ f (1) = 1 ∧ deriv f 0 = 0 ∧ 
    (∃ (x : ℝ), x ∈ Set.Ioo (-1 : ℝ) 1 ∧ deriv^[3] f x ≥ 3) := sorry

theorem not_always_topology (X : Type) : ¬ ∀ (T : Set (Set X)), T = {U | Set.Infinite (X \ U) ∨ U = ∅ ∨ U = Set.univ} → IsTopology T := sorry

theorem union_of_topologies_not_necessarily_topology (X : Type*) (T : Set (TopologicalSpace X)) : 
    ¬ ∀ (T_family : Set (TopologicalSpace X)), IsTopologicalSpace (⋃₀ T_family) := sorry

theorem exists_unique_largest_topology_contained_in_all {X : Type _} (T : ι → TopologicalSpace X) : 
    ∃! (τ : TopologicalSpace X), (∀ i, τ ≤ T i) ∧ ∀ (τ' : TopologicalSpace X), (∀ i, τ' ≤ T i) → τ' ≤ τ := sorry

theorem subbasis_generated_eq_intersection (X : Type*) (𝒜 : Set (Set X)) :
    TopologicalSpace.generateFrom 𝒜 = sInf {τ : TopologicalSpace X | 𝒜 ⊆ {s | IsOpen[τ] s}} := sorry

theorem rational_intervals_basis : TopologicalSpace.IsTopologicalBasis {s : Set ℝ | ∃ (a b : ℚ), a < b ∧ s = Set.Ioo (a : ℝ) (b : ℝ)} := sorry

theorem subspace_topology_equality (X : Type _) [TopologicalSpace X] (Y : Set X) [TopologicalSpace Y] (A : Set Y) : 
    Subtype.topologicalSpace (A : Set Y) = Subtype.topologicalSpace ((Subtype.val ⁻¹' A) : Set X) := sorry

theorem countable_basis_for_R2 : ∃ (basis : Set (Set (ℝ × ℝ))), Set.Countable basis ∧ (∀ (x : ℝ × ℝ), ∃ (s : Set (ℝ × ℝ)), s ∈ basis ∧ x ∈ s) ∧ (∀ (s₁ s₂ : Set (ℝ × ℝ)) (x : ℝ × ℝ), s₁ ∈ basis → s₂ ∈ basis → x ∈ s₁ ∩ s₂ → ∃ (s₃ : Set (ℝ × ℝ)), s₃ ∈ basis ∧ x ∈ s₃ ∧ s₃ ⊆ s₁ ∩ s₂) ∧ (∀ (U : Set (ℝ × ℝ)), IsOpen U → ∀ (x : ℝ × ℝ), x ∈ U → ∃ (s : Set (ℝ × ℝ)), s ∈ basis ∧ x ∈ s ∧ s ⊆ U) := sorry

theorem closed_set_of_le {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] [OrderedTopology Y] 
    (f g : X → Y) (hf : Continuous f) (hg : Continuous g) : IsClosed {x : X | f x ≤ g x} := sorry

theorem unique_continuous_extension (X Y : Type _) [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] 
    (A : Set X) (f : A → Y) (hf : Continuous f) (g : closure A → Y) (hg : Continuous g) 
    (h : ∀ x : A, g (Subtype.val x) = f x) : ∀ (g' : closure A → Y) (hg' : Continuous g') 
    (h' : ∀ x : A, g' (Subtype.val x) = f x), g = g' := sorry

theorem dictionary_order_metrizable : ∃ (d : ℝ × ℝ → ℝ × ℝ → ℝ), MetricSpace (ℝ × ℝ) ∧ ∀ (x y : ℝ × ℝ), d x y = dist x y := sorry

theorem not_uniformly_convergent : ¬ UniformConvergentOn (fun (n : ℕ) (x : ℝ) => x ^ n) (Set.Icc (0 : ℝ) 1) := sorry

theorem quotient_map_of_continuous_section {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] 
    (p : X → Y) (hp_cont : Continuous p) (f : Y → X) (hf_cont : Continuous f) 
    (hcomp : p ∘ f = id) : IsQuotientMap p := sorry

theorem open_map_restriction_to_open_domain (X Y : Type _) [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hp : IsOpenMap p) (A : Set X) (hA : IsOpen A) : IsOpenMap (fun (x : A) => p x) := sorry

theorem connected_union_of_connected_subspaces (X : Type*) [TopologicalSpace X] {A : Set X} (hA_conn : IsConnected A) {ι : Type*} (A_α : ι → Set X) (hA_α_conn : ∀ α, IsConnected (A_α α)) (h_nonempty_inter : ∀ α, (A ∩ A_α α).Nonempty) : IsConnected (A ∪ ⋃ α, A_α α) := sorry

theorem connected_subspace_intersects_boundary {X : Type _} [TopologicalSpace X] {A C : Set X} (hC : IsConnected C) (hA : A ⊆ X) (hC_inter_A : (C ∩ A).Nonempty) (hC_inter_compl : (C ∩ (X \ A)).Nonempty) : (C ∩ (frontier A)).Nonempty := sorry

theorem quotient_map_connected_preimage_implies_connected {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] 
    (p : X → Y) (hp : QuotientMap p) (h_preimage_connected : ∀ y, IsConnected (p⁻¹' {y})) 
    (hY_connected : IsConnected (Set.univ : Set Y)) : IsConnected (Set.univ : Set X) := sorry

theorem fixed_point_exists : ∀ (f : ℝ → ℝ), Continuous f → (∀ x, 0 ≤ x ∧ x ≤ 1 → f x ∈ Set.Icc (0 : ℝ) 1) → ∃ x, x ∈ Set.Icc (0 : ℝ) 1 ∧ f x = x := sorry

theorem component_of_identity_is_normal_subgroup (G : Type*) [TopologicalSpace G] [Group G] [TopologicalGroup G] : 
    let C := connectedComponent (1 : G) in 
    IsSubgroup C ∧ ∀ (g : G), g * C * g⁻¹ = C := sorry

theorem perfect_map_compactness (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] 
    (p : X → Y) (h_closed : IsClosedMap p) (h_cont : Continuous p) (h_surj : Function.Surjective p)
    (h_fiber_compact : ∀ y : Y, IsCompact (p⁻¹' {y})) : 
    (IsCompact (Set.univ : Set Y)) → (IsCompact (Set.univ : Set X)) := sorry

theorem T1_space_countably_compact_iff_limit_point_compact (X : Type*) [TopologicalSpace X] [T1Space X] : 
    (∀ (𝒰 : ℕ → Set X), (∀ i, IsOpen (𝒰 i)) → (⋃ i, 𝒰 i = Set.univ) → ∃ (s : Finset ℕ), ⋃ i ∈ s, 𝒰 i = Set.univ) ↔ 
    (∀ (A : Set X), Set.Infinite A → ∃ (x : X), x ∈ closure A ∧ x ∉ A) := sorry

theorem isometry_of_compact_metric_space_bijective (X : Type*) [MetricSpace X] [CompactSpace X] (f : X → X) (h_isometry : ∀ x y : X, dist (f x) (f y) = dist x y) : Function.Bijective f := sorry

theorem not_locally_compact_uniform_topology : ¬ LocallyCompactSpace (∀ n : ℕ, Set.Icc (0 : ℝ) 1) := sorry

theorem countable_dense_in_product (ι : Type*) [Countable ι] (X : ι → Type*) [∀ i, TopologicalSpace (X i)] [∀ i, SeparableSpace (X i)] : SeparableSpace (∀ i, X i) := sorry

theorem regular_implies_disjoint_closures (X : Type*) [TopologicalSpace X] [RegularSpace X] (x y : X) (h : x ≠ y) : 
    ∃ (U : Set X) (V : Set X), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ closure U ∩ closure V = ∅ := sorry

theorem order_topology_is_regular (α : Type _) [TopologicalSpace α] [OrderedTopology α] : RegularSpace α := sorry

theorem product_hausdorff_implies_factor_hausdorff {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, Nonempty (X i)] (h : T2Space (∀ i, X i)) : ∀ i, T2Space (X i) := sorry

theorem product_normal_implies_factor_normal {ι : Type*} {X : ι → Type*} [∀ α, TopologicalSpace (X α)]
    (h_nonempty : ∀ α, Nonempty (X α)) (h_normal : Normal (Π α, X α)) : ∀ α, Normal (X α) := sorry

theorem locally_compact_Hausdorff_is_completely_regular (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] : 
    CompletelyRegularSpace X := sorry

theorem metrizable_union_of_compact_Hausdorff_metrizable_closed_subspaces
    (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (X1 X2 : Set X) (hX1_closed : IsClosed X1) (hX2_closed : IsClosed X2)
    (hX_union : X1 ∪ X2 = Set.univ)
    (hX1_metrizable : MetrizableSpace (Subtype X1))
    (hX2_metrizable : MetrizableSpace (Subtype X2)) :
    MetrizableSpace X := sorry

theorem uniform_continuous_extension (X : Type*) (Y : Type*) [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] (A : Set X) (f : A → Y) (hf : UniformContinuous f) : ∃! (g : closure A → Y), UniformContinuous g ∧ ∀ (a : A), g (⟨a.val, subset_closure a.property⟩) = f a := sorry

theorem cube_root_of_one : ((-1 + Real.sqrt 3 * Complex.I) / 2) ^ 3 = 1 := sorry

theorem zero_product_property (a : F) (v : V) (h : a • v = (0 : V)) : a = (0 : F) ∨ v = (0 : V) := sorry

theorem exists_nonempty_subset_closed_under_scalar_mul_not_subspace : ∃ (U : Set (ℝ × ℝ)), U.Nonempty ∧ (∀ (c : ℝ) (x : ℝ × ℝ), x ∈ U → c • x ∈ U) ∧ ¬ (Submodule ℝ (ℝ × ℝ)).carrier U := sorry

theorem union_subspace_iff_subset (V : Type _) [AddCommGroup V] [Module ℝ V] (U W : Submodule ℝ V) : (U ⊔ W).carrier = U.carrier ∪ W.carrier ∧ Submodule ℝ V (U.carrier ∪ W.carrier) ↔ U ≤ W ∨ W ≤ U := sorry

theorem exists_subspace_with_null_and_range (V W : Type*) [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] W) : 
    ∃ (U : Submodule ℝ V), U ⊓ (LinearMap.ker T) = ⊥ ∧ LinearMap.range T = {T u | u ∈ U} := sorry

theorem invariant_sum_of_invariant_subspaces {V : Type _} [AddCommMonoid V] [Module ℝ V] (T : V →ₗ[ℝ] V) (U : Finset (Submodule ℝ V)) (hU : ∀ U' ∈ U, Submodule.map T U' ≤ U') : Submodule.map T (∑ U' in U, U') ≤ ∑ U' in U, U' := sorry

theorem same_eigenvalues_of_linear_maps (V : Type _) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (S T : Module.End ℂ V) : 
    {λ : ℂ | ∃ v : V, v ≠ 0 ∧ S (T v) = λ • v} = {λ : ℂ | ∃ v : V, v ≠ 0 ∧ T (S v) = λ • v} := sorry

theorem scalar_multiple_of_identity (V : Type _) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) : 
    (∀ (U : Submodule ℂ V), FiniteDimensional.finrank ℂ U = FiniteDimensional.finrank ℂ V - 1 → U ≤ Submodule.comap T U) → 
    ∃ (c : ℂ), T = c • LinearMap.id := sorry

theorem invariant_subspace_even_dimension (V : Type _) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (T : V →ₗ[ℝ] V) (h_no_eigenvalues : ¬∃ (v : V) (λ : ℝ), v ≠ 0 ∧ T v = λ • v) : ∀ (U : Submodule ℝ V), (∀ v ∈ U, T v ∈ U) → Even (FiniteDimensional.finrank ℝ U) := sorry

theorem cauchy_schwarz_weighted_sum (n : ℕ) (a b : ℕ → ℝ) : 
    (∑ j in Finset.range n, a j * b j) ^ 2 ≤ (∑ j in Finset.range n, (j : ℝ) * (a j) ^ 2) * (∑ j in Finset.range n, (b j) ^ 2 / (j : ℝ)) := sorry

theorem orthonormal_span_norm_sq_eq_sum_sq_inner (V : Type _) [NormedAddCommGroup V] [InnerProductSpace ℝ V] {m : ℕ} (e : Fin m → V) (hv_orthonormal : Orthonormal ℝ e) (v : V) : 
    ‖v‖ ^ 2 = ∑ i : Fin m, ‖⟪v, e i⟫_ℝ‖ ^ 2 ↔ v ∈ Submodule.span ℝ (Set.range e) := sorry

theorem not_subspace_of_normal_operators (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    (2 ≤ FiniteDimensional.finrank ℂ V) → ¬ IsSubmodule (Set.range (fun (T : V →ₗ[ℂ] V) => T)) (fun T => T ∘ T.adjoint = T.adjoint ∘ T) := sorry

theorem normal_operator_self_adjoint_iff_eigenvalues_real (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (T : V →ₗ[ℂ] V) (hT_normal : LinearMap.IsNormal T) : 
    T = LinearMap.adjoint T ↔ ∀ (λ : ℂ) (v : V), T v = λ • v → λ ∈ Set.range (fun (x : ℝ) => (x : ℂ)) := sorry

theorem exists_square_root_of_normal_operator (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (T : V →ₗ[ℂ] V) (hT : LinearMap.IsNormal T) : ∃ (S : V →ₗ[ℂ] V), S ^ 2 = T := sorry

theorem sum_of_reciprocals_not_integer : ∀ (n : ℕ) (hn : n ≥ 2), ¬ (∑ i in Finset.Icc 2 n, (1 : ℚ) / (i : ℚ)).den = 1 := sorry

theorem gcd_of_special_form (a : ℤ) (ha : a ≠ 0) (m n : ℕ) (hnm : n > m) : 
    Int.gcd (a ^ (2 ^ n) + 1) (a ^ (2 ^ m) + 1) = if a % 2 = 0 then 2 else 1 := sorry

theorem sum_recip_squarefree_diverges : ¬ ∃ (L : ℝ), Tendsto (λ (N : ℕ) => ∑ n in (Finset.filter (λ n => Squarefree n) (Finset.range N)).val, (1 : ℝ) / (n : ℝ)) atTop (𝓝 L) := sorry

theorem no_solution_in_integers : ¬∃ (x y : ℤ), 3 * x ^ 2 + 2 = y ^ 2 := sorry

theorem non_prime_factorial_congruence (n : ℕ) (hn : ¬ Nat.Prime n) : (n - 1)! ≡ 0 [MOD n] ∨ n = 4 := sorry

theorem primitive_root_iff_neg_primitive_root (p : ℕ) (hp : Nat.Prime p) (t : ℕ) (hp_form : p = 4 * t + 1) (a : ℤ) :
    (IsPrimitiveRoot a p) ↔ (IsPrimitiveRoot (-a) p) := sorry

theorem fermat_prime_primitive_root_three (n : ℕ) (hp : Nat.Prime (2 ^ n + 1)) (hfermat : ∃ k : ℕ, n = 2 ^ k) : 
    ∃ (a : ℕ) (ha : a < 2 ^ n + 1), IsPrimitiveRoot (a : ZMod (2 ^ n + 1)) (2 ^ n + 1) ∧ a = 3 := sorry

theorem sum_of_powers_mod_p (p : ℕ) (hp : Nat.Prime p) (k : ℕ) :
    (∑ i in Finset.Ico 1 p, i ^ k) % p = if p - 1 ∣ k then p - 1 else 0 := sorry

theorem exists_solution_x4_eq_two_mod_p_iff (p : ℕ) (hp : p ≡ 1 [MOD 4]) : 
    (∃ x : ℕ, x ^ 4 ≡ 2 [MOD p]) ↔ ∃ A B : ℕ, p = A ^ 2 + 64 * B ^ 2 := sorry

theorem sin_pi_over_twelve_is_algebraic : IsAlgebraic ℚ (Real.sin (π / 12)) := sorry

theorem holomorphic_const_imaginary_implies_const (Ω : Set ℂ) (hΩ : IsOpen Ω) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f Ω) (hconst : ∃ c : ℝ, ∀ z ∈ Ω, Complex.im (f z) = c) : ∃ c : ℂ, ∀ z ∈ Ω, f z = c := sorry

theorem power_series_n_z_pow_n_not_convergent_on_unit_circle : 
    ∀ (z : ℂ), Complex.abs z = 1 → ¬ Summable (λ n : ℕ => (n : ℂ) * z ^ n) := sorry

theorem power_series_convergence_on_unit_circle : 
    ∀ (z : ℂ), Complex.abs z = 1 → z ≠ 1 → Summable (λ n : ℕ ↦ z ^ n / (n : ℂ)) := sorry

theorem integral_sin_div_x : ∫ x in Set.Ioi (0 : ℝ), Real.sin x / x = π / 2 := sorry

theorem analytic_function_with_zero_coefficients_is_polynomial (f : ℂ → ℂ) (hf : AnalyticOn ℂ f Set.univ) 
    (h : ∀ z₀ : ℂ, ∃ n : ℕ, HasFPowerSeriesAt f (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ) z₀ ∧ 
    (ContinuousMultilinearMap.mkPiAlgebraFin ℂ n ℂ).toFormalMultilinearSeries.coeff n = 0) : 
    ∃ (p : Polynomial ℂ), ∀ z : ℂ, f z = Polynomial.eval z p := sorry

theorem integral_x_sin_x_over_x_sq_plus_a_sq (a : ℝ) (ha : a > 0) : ∫ (x : ℝ), (x * Real.sin x) / (x ^ 2 + a ^ 2) = π * Real.exp (-a) := sorry

theorem entire_injective_linear (f : ℂ → ℂ) (h_entire : Differentiable ℂ f) (h_inj : Function.Injective f) : 
    ∃ (a b : ℂ), a ≠ 0 ∧ ∀ z, f z = a * z + b := sorry

theorem zeros_of_bounded_holomorphic_function_in_unit_disc (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1)) 
    (hfb : ∃ M, ∀ z, ‖z‖ < 1 → ‖f z‖ ≤ M) (hf0 : ¬ ∀ z, ‖z‖ < 1 → f z = 0) 
    (zeros : ℕ → ℂ) (hzeros : ∀ n, f (zeros n) = 0 ∧ ‖zeros n‖ < 1) 
    (hinj : Function.Injective zeros) : 
    Summable fun n : ℕ => (1 : ℝ) - ‖zeros n‖ := sorry

theorem exists_derivative_negative (f : ℝ → ℝ) (h_diff : ContDiff ℝ ⊤ f) (h0 : f 0 = 0) (h1 : f 1 = 1) (h_nonneg : ∀ x, 0 ≤ f x) : 
    ∃ (n : ℕ) (x : ℝ), 0 < n ∧ deriv^[n] f x < 0 := sorry

theorem sequence_periodic_when_zero (a : ℝ) : 
    (∃ n, x a n = 0) → ∃ p, p > 0 ∧ ∀ n, x a (n + p) = x a n := sorry

theorem infinite_primes : ∀ n, ∃ p, n < p ∧ Nat.Prime p := sorry

theorem unique_positive_integers_satisfying_equation : ∃! (a n : ℕ), a > 0 ∧ n > 0 ∧ a ^ (n + 1) - (a + 1) ^ n = 2001 := sorry

theorem derivative_inequality : ∀ (f : ℝ → ℝ) (hf : ∀ x, ContDiffAt ℝ 3 f x) (hpos : ∀ x, 0 < f x ∧ 0 < deriv f x ∧ 0 < deriv (deriv f) x ∧ 0 < deriv (deriv (deriv f)) x) (hbound : ∀ x, deriv (deriv (deriv f)) x ≤ f x), ∀ x, deriv f x < 2 * f x := sorry

theorem exists_noninteger_sqrt (a b c : ℤ) : ∃ (n : ℕ), 0 < n ∧ ¬ (∃ (k : ℤ), (k : ℝ) = Real.sqrt ((n : ℝ)^3 + (a : ℝ) * (n : ℝ)^2 + (b : ℝ) * (n : ℝ) + (c : ℝ))) := sorry

theorem open_iff_no_limit_point_of_complement (U : Set M) : IsOpen U ↔ ∀ (x : M), ¬ (x ∈ closure (Uᶜ) ∧ x ∉ Uᶜ) := sorry

theorem every_subset_of_nat_is_clopen : ∀ (s : Set ℕ), IsClopen s := sorry

theorem exists_min_distance_between_compact_disjoint_nonempty_subsets {M : Type*} [MetricSpace M] {A B : Set M} (hA_compact : IsCompact A) (hB_compact : IsCompact B) (h_disjoint : Disjoint A B) (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty) : ∃ a₀ ∈ A, ∃ b₀ ∈ B, ∀ a ∈ A, ∀ b ∈ B, dist a₀ b₀ ≤ dist a b := sorry

