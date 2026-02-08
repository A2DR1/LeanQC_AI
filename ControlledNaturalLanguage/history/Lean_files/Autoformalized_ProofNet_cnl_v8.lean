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

theorem permutations_id {S : Type*} [Fintype S] (σ : Equiv.Perm S) (τ : Equiv.Perm S) 
  (h1 : ∀ x : S, σ x ≠ x → τ x = x) 
  (h2 : ∀ x : S, τ x ≠ x → σ x = x) 
  (h3 : σ ∘ τ = Equiv.refl S) : 
  σ = Equiv.refl S ∧ τ = Equiv.refl S := sorry

theorem left_annihilator_is_ideal (R : Type*) [CommRing R] (a : R) : Ideal R (fun x => x * a = 0) := sorry

theorem sum_convergence : 
  let D := {z : ℂ | Complex.abs z < 1};
  ∀ (f : D → ℂ), HolomorphicOn f D → 
  (∃ (M : ℝ), ∀ (z : D), Complex.abs (f z) ≤ M) → 
  (∃ (z : D), f z ≠ 0) → 
  ∀ (Z : ℕ → D), (∀ (n : ℕ), f (Z n) = 0) → 
  (∀ (n : ℕ), Complex.abs (Z n) < 1) → 
  Summable fun n => 1 - Complex.abs (Z n) := sorry

theorem limsup_add_le_add_limsup (a b : ℕ → ℝ) (ha : ∃ l, Filter.limsup (fun n => a n) Filter.atTop = l) (hb : ∃ m, Filter.limsup (fun n => b n) Filter.atTop = m) (hsum : Filter.limsup (fun n => a n) Filter.atTop + Filter.limsup (fun n => b n) Filter.atTop ≠ ⊤) : Filter.limsup (fun n => a n + b n) Filter.atTop ≤ Filter.limsup (fun n => a n) Filter.atTop + Filter.limsup (fun n => b n) Filter.atTop := sorry

theorem subset_properties : ∃ (U : Set (ℝ × ℝ)), U = {(x, y) | x = 0 ∨ y = 0} ∧ Set.Nonempty U ∧ (∀ (c : ℝ) (p : ℝ × ℝ), p ∈ U → (c • p) ∈ U) ∧ ¬ (∀ (p q : ℝ × ℝ), p ∈ U → q ∈ U → p + q ∈ U) := sorry

theorem subgroup_power_order_fixed_by_automorphisms (G : Type*) [AddCommGroup G] (p : ℕ) [Nat.Prime p] (m n : ℕ) (hpm : ¬p ∣ m) (H : AddSubgroup G) (hG : Nat.card G = p ^ n * m) (hH : Nat.card H = p ^ n) (f : AddAut G) : AddSubgroup.map (f.toAddMonoidHom) H = H := sorry

theorem quotient_of_solvable_is_solvable {G : Type*} [Group G] [IsSolvable G] (N : Subgroup G) [N.Normal] : IsSolvable (G ⧸ N) := sorry

theorem rational_intervals_basis : TopologicalSpace.IsTopologicalBasis {U | ∃ (a b : ℚ), a < b ∧ U = Set.Ioo (↑a) (↑b)} := sorry

theorem groups_of_order_pq_isomorphic (p : ℕ) (q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p > q) (hdiv : q ∣ (p - 1)) (G1 : Type*) [Group G1] (hG1 : ¬CommGroup.toGroup (CommGroup.mk G1 _)) (hsize1 : Nat.card G1 = p * q) (G2 : Type*) [Group G2] (hG2 : ¬CommGroup.toGroup (CommGroup.mk G2 _)) (hsize2 : Nat.card G2 = p * q) : Nonempty (G1 ≃* G2) := sorry

theorem parallelogram_law {k : ℕ} (x y : EuclideanSpace ℝ (Fin k)) : ‖x + y‖^2 + ‖x - y‖^2 = 2 * ‖x‖^2 + 2 * ‖y‖^2 := sorry

theorem exists_prime_order_cyclic_group (G : Type*) [Group G] (h : ∀ (H : Subgroup G), H = ⊥ ∨ H = ⊤) : ∃ (p : ℕ), Nat.Prime p ∧ Nonempty (G ≃* Multiplicative (ZMod p)) ∧ Nat.card G = p := sorry

theorem integral_domain_to_principal_ideal_domain (R : Type*) [CommRing R] [IsDomain R] 
  (hbezout : ∀ (a b : R), a ≠ 0 → b ≠ 0 → ∃ r s : R, gcd a b = r * a + s * b)
  (hacc : ∀ (a : ℕ → R), (∀ i : ℕ, a i ≠ 0) → (∀ i : ℕ, a (i + 1) ∣ a i) → ∃ N : ℕ, ∃ (u : R) (hu : IsUnit u), ∀ n ≥ N, a n = u * a N) : 
  IsPrincipalIdealRing R := sorry

theorem exists_normal_Sylow_subgroup (G : Type*) [Group G] (hG : Nat.card G = 56) (p : ℕ) (hp : Nat.Prime p) (hdiv : p ∣ 56) : ∃ (H : Subgroup G), IsSylow p H ∧ Subgroup.Normal H := sorry

theorem unit_of_one_minus_ab {R : Type*} [CommRing R] (h1 : (1 : R) ∈ R) (h1_ne_zero : (1 : R) ≠ 0) (a : R) (n : ℕ) (h_pow : a ^ n = 0) (b : R) : IsUnit (1 - a * b) := sorry

theorem exists_maximal_subgroup_containing_proper_subgroup (G : Type*) [Group G] [Fintype G] (H : Subgroup G) (hH : H ≠ ⊤) : ∃ M : Subgroup G, H ≤ M ∧ M ≠ ⊤ ∧ ∀ K : Subgroup G, M ≤ K → K = M ∨ K = ⊤ := sorry

theorem primitive_root_three_mod_p (n : ℕ) (p : ℕ) (hp : p = 2^n + 1) (hprime : Nat.Prime p) : IsPrimitiveRoot (3 : ZMod p) (p - 1) := sorry

theorem not_locally_compact : ¬ LocallyCompactSpace (∀ n : ℕ, Set.Icc (0 : ℝ) 1) := sorry

theorem product_eq_intersection {R : Type*} [Ring R] (I J : Ideal R) (h : I + J = ⊤) : I * J = I ⊓ J := sorry

theorem center_image_in_center {R : Type*} [Ring R] {S : Type*} [Ring S] (φ : R →+* S) 
(hφ : Function.Surjective φ) (z : R) (hz : ∀ r : R, z * r = r * z) : 
∀ s : S, φ z * s = s * φ z := sorry

theorem irreducibles_in_R (n : ℕ) (hn_gt : n > 3) (hn_squarefree : Squarefree n) : 
  Irreducible (2 : {a : ℤ // ∃ b : ℤ, a = a + b * Real.sqrt (-↑n)}) ∧ 
  Irreducible (Real.sqrt (-↑n) : {a : ℤ // ∃ b : ℤ, a = a + b * Real.sqrt (-↑n)}) ∧ 
  Irreducible ((1 + Real.sqrt (-↑n)) : {a : ℤ // ∃ b : ℤ, a = a + b * Real.sqrt (-↑n)}) := sorry

theorem exists_pow_eq_identity {G : Type*} [Fintype G] (· : G → G → G) [Group G] (e : G) (a : G) : ∃ n : ℕ, 1 ≤ n ∧ (Nat.iterate (fun x => · a x) n e) = e := sorry

theorem subspace_dim_even {V : Type*} [AddCommGroup V] [Module ℝ V] (T : V →ₗ[ℝ] V) (h_no_eigen : ∀ (λ : ℝ), ¬∃ (v : V), v ≠ 0 ∧ T v = λ • v) (U : Submodule ℝ V) (h_inv : ∀ u ∈ U, T u ∈ U) : Even (FiniteDimensional.finrank ℝ U) := sorry

theorem norm_sq_sum_diff_eq_four (z : ℂ) (hz : z * Complex.conj z = 1) : |1 + z|^2 + |1 - z|^2 = 4 := sorry

theorem cauchy_schwarz_special_case (n : ℕ) (a : Fin n → ℝ) (b : Fin n → ℝ) : (∑ j, a j * b j)^2 ≤ (∑ j, (↑j + 1) * a j^2) * (∑ j, b j^2 / (↑j + 1)) := sorry

theorem product_normal_implies_components_normal (A : Type*) (X : A → Type*) [∀ α, TopologicalSpace (X α)] [∀ α, Nonempty (X α)] (hP : Normal (∀ α, X α)) : ∀ α, Normal (X α) := sorry

theorem no_nonzero_orthogonal_vector (x : ℝ^1) (h : k = 1) : ¬∃ (y : ℝ^1), y ≠ 0 ∧ x · y = 0 := sorry

theorem unique_extension_hausdorff {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] [T2Space Y] {A : Set X} (f : A → Y) (hf : Continuous f) (g : closure A → Y) (hg : Continuous g) (heq : ∀ x ∈ A, g ⟨x, subset_closure ‹_›⟩ = f x) (h : closure A → Y) (hh : Continuous h) (heq' : ∀ x ∈ A, h ⟨x, subset_closure ‹_›⟩ = f x) : h = g := sorry

theorem quotient_of_gaussian_integers_field (q : ℤ) (hq : Nat.Prime (Int.natAbs q)) (hq_mod : q ≡ 3 [ZMOD 4]) : IsField (GaussianInt.quotient (Ideal.span ({q} : Set GaussianInt))) ∧ Fintype.card (GaussianInt.quotient (Ideal.span ({q} : Set GaussianInt))) = q^2 := sorry

theorem countable_compactness_iff_limit_point_compactness (X : Type*) (T : TopologicalSpace X) [T1Space X] : 
  (∀ (U : Set (Set X)), U.Countable → (∀ s ∈ U, IsOpen s) → ⋃₀ U = Set.univ → ∃ (V : Finset (Set X)), (∀ s ∈ V, s ∈ U) ∧ ⋃₀ (↑V : Set (Set X)) = Set.univ) ↔ 
  (∀ (A : Set X), Set.Infinite A → ∃ x ∈ Set.univ, ClusterPt x (Filter.principal A)) := sorry

theorem nested_compact_sets_nonempty (K : ℕ → Set ℝ) 
(h_nonempty : ∀ n, Set.Nonempty (K n)) 
(h_compact : ∀ n, IsCompact (K n)) 
(h_nested : ∀ n, K (n + 1) ⊆ K n) : 
Set.Nonempty (⋂ n, K n) := sorry

theorem no_continuous_extension (E : Set ℝ) (f : E → ℝ) (hf : ContinuousOn f E) : ¬∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, g x = f x := sorry

theorem normal_operators_not_subspace (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (h : FiniteDimensional.finrank ℂ V ≥ 2) : ¬IsSubmodule (L(V)) (N : Set (L(V))) := sorry

theorem self_adjoint_of_eigenvalue_real {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (T : V →ₗ[ℂ] V) (hT : LinearMap.IsNormal T) (hλ_real : ∀ (λ : ℂ), HasEigenvalue T λ → λ ∈ ℝ) : T = LinearMap.adjoint T := sorry

theorem subgroup_of_prime_index_normal {p : ℕ} (hp : Nat.Prime p) {α : ℕ} (G : Type*) [Group G] (hG : Nat.card G = p ^ α) (H : Subgroup G) (hH : Subgroup.index H = p) : Subgroup.Normal H := sorry

theorem exists_normal_Sylow_p_subgroup (G : Type*) [Group G] (hG : Nat.card G = 351) (p : ℕ) (hp : Nat.Prime p) (hdiv : p ∣ 351) : ∃ (P : Subgroup G), IsSylow p P ∧ Subgroup.Normal P := sorry

theorem p_irreducible_over_F31 : Irreducible (Polynomial.map (Int.castRingHom (ZMod 31)) (Polynomial.C (x : ZMod 31) ^ 3 - Polynomial.C 9)) := sorry

theorem exists_disjoint_open_nbhd_closure {X : Type*} [TopologicalSpace X] [RegularSpace X] (x y : X) (hxy : x ≠ y) : ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ closure U ∩ closure V = ∅ := sorry

theorem nonzero_product_in_subring {F : Type*} [Field F] (R : Set F) [Subring R] (h1 : (1 : F) ∈ R) (x y : F) (hx : x ∈ R) (hy : y ∈ R) (hx0 : x ≠ 0) (hy0 : y ≠ 0) : x * y ≠ 0 := sorry

theorem exists_boundary_point_in_connected_set (X : Type*) [TopologicalSpace X] (A C : Set X) (hC : IsConnected C) (hx : ∃ x ∈ C, x ∈ A) (hy : ∃ y ∈ C, y ∈ X \ A) : ∃ z ∈ C, z ∈ frontier A := sorry

theorem inv_eq_pow_of_order {G : Type*} [Group G] (x : G) (n : ℕ) (hn : n > 0) (hx : orderOf x = n) : x⁻¹ = x^(n - 1) := sorry

theorem sum_pow_mod_p (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (S : Finset ℕ) (hS : S = Finset.Icc 1 (p - 1)) (f : ℕ → ℕ) (hf : ∀ x ∈ S, f x = x ^ k % p) : (¬ (p - 1) ∣ k → Finset.sum S f % p = 0) ∧ ((p - 1) ∣ k → Finset.sum S f % p = p - 1) := sorry

theorem eigenvalues_conjugate {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] (S T : Module.End F V) (λ : F) : (∃ (v : V), v ≠ 0 ∧ Module.End.toFun (S ∘ₗ T) v = λ • v) ↔ (∃ (w : V), w ≠ 0 ∧ Module.End.toFun (T ∘ₗ S) w = λ • w) := sorry

theorem product_group_abelian_iff_components_abelian {A : Type*} {B : Type*} [Group A] [Group B] (G : Type*) [Group G] (hG : G = A × B) (add_A : A → A → A) (add_B : B → B → B) (add_G : G → G → G) (hadd : ∀ (a1 a2 : A) (b1 b2 : B), add_G (a1, b1) (a2, b2) = (add_A a1 a2, add_B b1 b2)) : CommGroup G ↔ CommGroup A ∧ CommGroup B := sorry

theorem exists_nonzero_integer_in_ideal (I : Ideal (GaussianInt ℤ)) (hI : I ≠ ⊥) : ∃ (z : ℤ), z ≠ 0 ∧ ↑z ∈ I := sorry

theorem exists_non_identity_element_of_order_two {G : Type*} [Fintype G] (e : G) (· : G × G → G) [Group G] (hG : Fintype.card G % 2 = 0) : ∃ a : G, a ≠ e ∧ · (a, a) = e := sorry

theorem polynomial_irreducible : Irreducible (Polynomial.C (1 : ℚ) * Polynomial.X ^ 3 + Polynomial.C (3 : ℚ) * Polynomial.X + Polynomial.C (2 : ℚ)) := sorry

theorem exists_j_for_conjugate {G : Type*} [Group G] (h : ∀ (H : Subgroup G), Subgroup.Normal H) (a : G) (b : G) : ∃ (j : ℤ), b * a = a^j * b := sorry

theorem field_hom_injective {F K : Type*} [Field F] [Field K] (φ : F →+* K) : Function.Injective φ := sorry

theorem group_of_order_product_primes_not_simple {G : Type*} [Group G] (p q : ℕ) [Nat.Prime p] [Nat.Prime q] (hG : Nat.card G = p * q) (hpq : p ≤ q) : ¬IsSimpleGroup G := sorry

theorem frobenius_power {F : Type*} [Field F] (p : ℕ) (hchar : Ring.Char F = p) (hp : p ≠ 0) (n : ℕ) (hn : n > 0) (m : ℕ) (hm : m = p ^ n) (a b : F) : (a + b) ^ m = a ^ m + b ^ m := sorry

theorem exists_int_mul {a b : ℤ} (h : ∃ c : GaussianInt, (b : GaussianInt) = (a : GaussianInt) * c) : ∃ d : ℤ, b = a * d := sorry

theorem derivative_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (hcont : Continuous f) (hpos : ∀ x, f x > 0) (hpos' : ∀ x, deriv f x > 0) (hpos'' : ∀ x, deriv (deriv f) x > 0) (hpos''' : ∀ x, deriv (deriv (deriv f)) x > 0) (hbound : ∀ x, deriv (deriv (deriv f)) x ≤ f x) : ∀ x, deriv f x < 2 * f x := sorry

theorem union_of_topologies_not_necessarily_topology (X : Type*) (I : Type*) (T : I → TopologicalSpace X) : ¬∀ (s : Set (Set X)), (∀ (α : I), s = T α) → TopologicalSpace X := sorry

theorem subspace_topology_inheritance {X : Type*} [TopologicalSpace X] (Y : Set X) [TopologicalSpace Y] [TopologicalSpace.Subtype Y] (A : Set Y) : TopologicalSpace.subspace A = TopologicalSpace.subspace (Subtype.val '' A) := sorry

theorem exists_bijective_linear_map : ∃ (n : ℤ⁺), ∃ (f : (Fin (↑n) → ℝ) →ₗ[ℚ] ℝ), Function.Bijective f := sorry

theorem comm_power_identity {G : Type*} [Group G] (n : ℤ) (hn : n > 1) (h : ∀ (a b : G), (a * b)^n = a^n * b^n) (a b : G) : (a * b * a⁻¹ * b⁻¹)^(n * (n - 1)) = 1 := sorry

theorem characteristic_subgroup_of_normal_is_normal {G : Type*} [Group G] (H K : Subgroup G) (hHK : H ≤ K) (hHchar : Subgroup.Characteristic H K) (hKnorm : Subgroup.Normal K) : Subgroup.Normal H := sorry

theorem quotient_map_of_section {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (f : Y → X) (hp : Continuous p) (hf : Continuous f) (h : ∀ y, p (f y) = y) : QuotientMap p := sorry

theorem exists_infinite_minimal_primes (R : Type*) [CommRing R] (I : Ideal R) (S : Type*) [CommRing S] (hS : S = R ⧸ I) : ∃ (P : Set (Ideal S)), Set.Infinite P ∧ ∀ (p ∈ P), Ideal.IsPrime p ∧ ∀ (q : Ideal S), Ideal.IsPrime q → q ≤ p → q = p := sorry

theorem connected_space_of_quotient_map_with_connected_fibers {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y] (p : X → Y) (hp : QuotientMap p) (hfib : ∀ y ∈ Y, IsConnected (p⁻¹' {y})) (hY : IsConnected Y) : IsConnected X := sorry

theorem factorial_mod_non_prime (n : ℕ) (h₁ : n > 1) (h₂ : ¬Nat.Prime n) (h₃ : n ≠ 4) : (n - 1)! ≡ 0 [MOD n] := sorry

theorem f_comm {G : Type*} [Group G] (a : G) (b : G) (f : G × G → ℝ) (hf : ∀ (x y : G), f (x, y) = |↑(x * y)|) : f (a, b) = f (b, a) := sorry

theorem subgroup_intersection_trivial {G : Type*} [Group G] (A : Subgroup G) [hA : Subgroup.Normal A] (b : G) (hb : orderOf b = Nat.Prime.out (Nat.Prime p)) (hbnin : b ∉ A) : Subgroup.comap (Subgroup.subtype A) (Subgroup.closure {b}) = ⊥ := sorry

theorem sum_sqrt_div_n_converges (a : ℕ → ℝ) (ha_nonneg : ∀ n, a n ≥ 0) (ha_sum : Summable a) : Summable (fun n => Real.sqrt (a n) / (n : ℝ)) := sorry

theorem exists_noncontinuous_function_with_symmetric_limit_zero : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Tendsto (fun h ↦ f (x + h) - f (x - h)) (𝓝 0) (𝓝 0)) ∧ ¬Continuous f := sorry

theorem comm_group_of_automorphism_condition {G : Type*} [Fintype G] (op : G × G → G) [Group G] (σ : G → G) (hσ : Group.IsAutomorphism σ) (hσ_id : ∀ g : G, σ g = g ↔ g = 1) (hσ_sq : σ ∘ σ = id) : ∀ a b : G, op (a, b) = op (b, a) := sorry

theorem exists_fourth_root_iff_sum_of_squares (p : ℕ) (hp : Nat.Prime p) (hp_mod : p ≡ 1 [MOD 4]) : (∃ x ∈ Finset.range p, (x^4) % p = 2 % p) ↔ ∃ A B : ℕ, p = A^2 + 64 * B^2 := sorry

theorem exists_scalar_for_linear_map_eq_scalar_mul_id {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] (T : Module.End F V) (h : ∀ (U : Submodule F V), FiniteDimensional.finrank F U = FiniteDimensional.finrank F V - 1 → U.map T ≤ U) : ∃ (λ : F), T = λ • LinearMap.id := sorry

theorem zero_set_closed (X : Type*) [MetricSpace X] (f : X → ℝ) (hf : Continuous f) : IsClosed {p : X | f p = 0} := sorry

theorem open_iff_not_limit_point_complement (M : Type*) [MetricSpace M] (U : Set M) (C : Set M := M \ U) : IsOpen U ↔ ∀ p ∈ U, ¬IsLimitPoint p C := sorry

theorem uncountable_set_diff_perfect_set_countable {k : ℕ} (E : Set (Fin k → ℝ)) (hE : ¬Set.Countable E) (P : Set (Fin k → ℝ) := {x | ∀ U, IsOpen U → x ∈ U → ¬Set.Countable (U ∩ E)}) : Set.Countable (E \ P) := sorry

theorem rational_boxes_basis : IsTopologicalBasis {s : Set (ℝ × ℝ) | ∃ (a b c d : ℚ), s = Set.Ioo (↑a) (↑b) ×ˢ Set.Ioo (↑c) (↑d) ∧ (a < b) ∧ (c < d)} := sorry

theorem group_bijection_inverse_abelian (G : Type*) [Fintype G] (op : G × G → G) [Group G] (φ : G → G) (hφ : Bijective φ) (hφ_mul : ∀ x y, φ (op x y) = op (φ x) (φ y)) (S : Set G) (hS : S = {x | φ x = (op x (1 : G))⁻¹}) (hS_card : Fintype.card S > (3/4) * Fintype.card G) : (∀ y, φ y = (op y (1 : G))⁻¹) ∧ ∀ x y, op x y = op y x := sorry

theorem union_of_proper_subspaces_not_equal_V {F : Type*} [Field F] [Infinite F] {V : Type*} [AddCommGroup V] [Module F V] (n : ℕ) (S : Finset (Submodule F V)) (hS : Finset.card S = n) (hproper : ∀ W ∈ S, W ≠ ⊤) : ⋃₀ (Submodule.toAddSubgroup '' (S : Set (Submodule F V))) ≠ ⊤ := sorry

theorem open_set_decomposition (U : Set ℝ) (hU : IsOpen U) (~ : U × U → Prop) 
  (h~ : ∀ (x y : U), x ~ y ↔ Set.Icc (min (x.val) (y.val)) (max (x.val) (y.val)) ⊆ U) 
  (equiv_rel : Equivalence ~) :
  let classes := Quotient (Setoid.mk ~ equiv_rel);
  let I_C := fun (C : classes) => ⋃ (x : U) (hx : Quotient.mk' x = C), 
    Set.Icc (Subtype.val x) (Subtype.val x);
  U = ⋃ (C : classes), I_C C ∧ 
  (Set.Countable (Set.range I_C) ∧ ∀ (C₁ C₂ : classes), C₁ ≠ C₂ → Disjoint (I_C C₁) (I_C C₂)) := sorry

theorem commutes_with_a {R : Type*} [Ring R] (a : R) (ha : a^2 = 0) (x : R) : let b := a * x + x * a; b * a = a * b := sorry

theorem cube_root_of_unity (z : ℂ) (hz : z = (-1 + Real.sqrt 3 * Complex.I) / 2) : z ^ 3 = 1 := sorry

theorem group_not_simple {G : Type*} [Group G] (hG : Nat.card G = 2907) : ¬IsSimpleGroup G := sorry

theorem holomorphic_with_constant_imaginary_part_is_constant (Ω : Set ℂ) (hΩ : IsOpen Ω) (f : Ω → ℂ) (hf : DifferentiableOn ℂ f Ω) (c : ℝ) (hc : ∀ z ∈ Ω, Complex.im (f z) = c) : ∃ C : ℂ, ∀ z ∈ Ω, f z = C := sorry

theorem not_simple_group_of_order_224 (G : Type*) [Group G] (hG : Nat.card G = 224) (n₇ : ℕ) (hn₇ : Sylow.normalizerCondition G → n₇ = Nat.card (Sylow G 7)) : ¬IsSimpleGroup G := sorry

theorem isometry_on_compact_is_bijective_homeomorphism {X : Type*} [MetricSpace X] (hX : IsCompact (univ : Set X)) (f : X → X) (hf : ∀ x y, dist (f x) (f y) = dist x y) : Function.Bijective f ∧ Homeomorph f := sorry

theorem exists_prime_factor_not_in_S (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ p ≡ 3 [MOD 4]) (hS_fin : S.Finite) : 
    let n := (∏ p in S, p) * 4 - 1;
    n ≡ 3 [MOD 4] ∧ ∃ q : ℕ, Nat.Prime q ∧ q ∣ n ∧ q ≡ 3 [MOD 4] ∧ q ∉ S := sorry

theorem series_convergence (p : ℝ) (hp : p > 1) (f : ℕ → ℝ) (hf : ∀ k ≥ 2, f k = 1 / (k * (Real.log ↑k)^p)) : Summable f := sorry

theorem exists_derivative_negative (f : ℝ → ℝ) (hDiff : ∀ n, ContDiff ℝ n f) (h0 : f 0 = 0) (h1 : f 1 = 1) (hNonNeg : ∀ x, f x ≥ 0) : ∃ (n : ℕ) (x : ℝ), iteratedDeriv n f x < 0 := sorry

theorem neg_unit_is_unit {R : Type*} [Ring R] (u : R) (hu : IsUnit u) : IsUnit (-u) := sorry

theorem order_of_inv_eq_order_of {G : Type*} [Group G] (x : G) : orderOf x = orderOf (x⁻¹) := sorry

theorem exists_square_root_of_normal_operator (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (T : V →ₗ[ℂ] V) (hT : LinearMap.IsNormal T) : ∃ (S : V →ₗ[ℂ] V), S ∘ S = T := sorry

theorem exists_nonzero_complex_square_negative (ℂ : Type*) [Field ℂ] [OrderedField ℂ] : ∃ z : ℂ, z ≠ 0 ∧ z^2 < 0 := sorry

theorem sequence_periodic (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1) (hx1 : x 1 = a) (hx2 : x 2 = a) (hrec : ∀ n ≥ 2, x (n + 1) = 2 * x n * x (n - 1) - x (n - 2)) (hex : ∃ n, x n = 0) : Periodic x := sorry

theorem mul_assoc_ZnZ (n : ℕ) (a b c : ℤ) : (Quotient.mk (Int.instModEqRel n) a * Quotient.mk (Int.instModEqRel n) b) * Quotient.mk (Int.instModEqRel n) c = Quotient.mk (Int.instModEqRel n) a * (Quotient.mk (Int.instModEqRel n) b * Quotient.mk (Int.instModEqRel n) c) := sorry

theorem compact_space_of_proper_surjective_continuous_closed_map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hcont : Continuous p) (hsurj : Function.Surjective p) (hclosed : IsClosedMap p) (hproper : ∀ y ∈ Y, IsCompact (p⁻¹' {y})) (hY : IsCompact Y) : IsCompact X := sorry

theorem finite_subgroups_with_coprime_orders_intersect_trivially {G : Type*} [Group G] (H : Subgroup G) [Finite ↥H] (K : Subgroup G) [Finite ↥K] (hcoprime : Nat.gcd (Nat.card ↥H) (Nat.card ↥K) = 1) : H ⊓ K = ⊥ := sorry

theorem not_simple_group_of_order_462 {G : Type*} [Group G] (hG : Nat.card G = 462) : ¬IsSimpleGroup G := sorry

theorem H_not_integer (n : ℕ) (hn : n ≥ 2) : ¬(H n ∈ ℤ) := sorry

theorem exists_min_distance_between_compact_sets {M : Type*} [MetricSpace M] (A B : Set M) (hA : IsCompact A) (hB : IsCompact B) (hDisj : Disjoint A B) (hA_nonempty : Set.Nonempty A) (hB_nonempty : Set.Nonempty B) : ∃ a0 ∈ A, ∃ b0 ∈ B, ∀ a ∈ A, ∀ b ∈ B, dist a0 b0 ≤ dist a b := sorry

theorem constant_function (f : ℝ → ℝ) (h : ∀ x y : ℝ, |f x - f y| ≤ (x - y)^2) : ∃ c : ℝ, ∀ x : ℝ, f x = c := sorry

theorem exists_nonzero_annihilator (R : Type*) [Ring R] (p : ℕ → R) (hp : ∃ (n : ℕ) (a : ℕ → R), (∀ k ≤ n, p k = a k) ∧ a n ≠ 0) : ∃ b ∈ R, b ≠ 0 ∧ ∀ x : ℕ, b * p x = 0 := sorry

theorem primitive_root_iff_neg_primitive_root (p : ℕ) (hp : Nat.Prime p) (hp_mod : p ≡ 1 [MOD 4]) (t : ℕ) (ht : p = 4 * t + 1) (a : ℤ) (ha : Int.gcd a p = 1) : IsPrimitiveRoot (a : ZMod p) p ↔ IsPrimitiveRoot (-a : ZMod p) p := sorry

theorem sylow_intersection_unique {G : Type*} [Group G] (P : Subgroup G) [hP : Sylow P] [Normal P] (H : Subgroup G) : IsSylow (Subgroup.carrier P ∩ Subgroup.carrier H) ∧ ∀ (Q : Subgroup H), IsSylow Q → Q = Subgroup.carrier P ∩ Subgroup.carrier H := sorry

theorem limit_of_difference_quotient (f : ℝ → ℝ) (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hlim : Tendsto (fun x ↦ deriv f x) atTop (𝓝 0)) (g : ℝ → ℝ) (hg : ∀ x > 0, g x = f (x + 1) - f x) : Tendsto g atTop (𝓝 0) := sorry

