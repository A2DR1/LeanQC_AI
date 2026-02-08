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

theorem rational_number_mul_ironic (r : ℚ) (hr : r ≠ 0) (x : ℝ) (hx : Irrational x) :
    Irrational (r * x) := by sorry

theorem lower_bound (α : Type*) [PartialOrder α] (E : Set α)
  (hE : E.Nonempty) (α₀ : α) (h₁ : α₀ ∈ lowerBounds E) :
  α₀ ≤ sSup E :=
sorry

theorem no_total_order : ¬ ∃ f : ℂ → ℂ, Function.Injective f ∧ ∀ x y, f x = f y → x = y ∧ (∀ x, f x ≠ 0) ∧ (∀ x, f x * f (x + 1) > 0) ∧ (∀ x, f x * f (x - 1) < 0) := by sorry

theorem sum_of_norms (n : ℕ) (f : Fin n → ℂ) :
    abs (∑ i : Fin n, f i) ≤ ∑ i : Fin n, abs (f i) :=
sorry

theorem norm_1 (z : ℂ) (hz : abs z = 1) :
    abs (1 + z) ^ 2 + abs (1 - z) ^ 2 = 4 := by sorry

theorem norm_eq (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖x + y‖^2 + ‖x - y‖^2 = 2 * ‖x‖^2 + 2 * ‖y‖^2 :=
sorry

theorem no_zero_divisor {R : Type*} [CommRing R] (x : R) :
  ¬ ∃ y : R, y ≠ 0 ∧ x * y = 0 :=
sorry

theorem separated_set {X : Type*} [MetricSpace X]
  {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
  (hAB : Disjoint A B) :
  SeparatedSet A B :=
sorry

theorem countable_base {K : Type*} [MetricSpace K] [CompactSpace K] :
    ∃ B : Set (Set K), Set.Countable B ∧ IsTopologicalBasis B :=
sorry

theorem uncountable_set_not_in_condensation_points {k : ℕ} (E : Set (EuclideanSpace ℝ (Fin k))) (hE : ¬ Countable E)
    (P : Set (EuclideanSpace ℝ (Fin k))) (hP : P = {x | ∀ U ∈ 𝓝 x, (P ∩ E).Nonempty ∧ ¬ Countable (P ∩ E)}) :
    Set.Countable (E \ P) :=
sorry

theorem segmentUnion (U : Set ℝ) (hU : IsOpen U) :
    ∃ (f : ℕ → Set ℝ), (∀ i j, i ≠ j → f i ∩ f j = ∅) ∧
      (∀ i, ∃ a b, f i = Ioo a b) ∧
      (∀ x, x ∈ U ↔ ∃ i, x ∈ f i) ∧
      Set.Countable {i | ∃ a b, f i = Ioo a b} :=
sorry

theorem Tendsto_sqrt : Tendsto (λ n => sqrt (n ^ 2 + n) - n) atTop (𝓝 (1 / 2)) :=
sorry

theorem limsup_add
  (a b : ℕ → ℝ)
  (h : limsup a + limsup b ≠ 0) :
  limsup (λ n => a n + b n) ≤ limsup a + limsup b :=
sorry

theorem sum_of_squares_convergence
  (a : ℕ → ℝ)
  (h : ∃ L, Tendsto (λ n => (∑ i in range n, a i)) atTop (𝓝 L))
  (ha : ∀ n, 0 ≤ a n) :
  ∃ L, Tendsto (λ n => (∑ i in range n, sqrt (a i) / n)) atTop (𝓝 L) :=
sorry

theorem cauchyProduct
  (a b : ℕ → ℝ)
  (ha : ∃ y, Tendsto (λ n => (∑ i in range n, |a i|)) atTop (𝓝 y))
  (hb : ∃ y, Tendsto (λ n => (∑ i in range n, |b i|)) atTop (𝓝 y)) :
  ∃ y, Tendsto (λ n => (∑ i in range n, (∑ j in range (i + 1), a j * b (i - j)))) atTop (𝓝 y) :=
sorry

theorem
  (X : Type*) [MetricSpace X] [CompleteSpace X]
  (E : ℕ → Set X)
  (hE : ∀ n, IsClosed (E n))
  (hE1 : ∀ n, E n ≠ ∅)
  (hE2 : ∀ n, BddAbove (E n))
  (hE3 : ∀ n, E n ⊆ E (n + 1))
  (hE4 : Tendsto (λ n => (MeasureTheory.volume (E n)).toReal) atTop (𝓝 0)) :
  ∃! x, ∀ n, x ∈ E n :=
sorry

theorem non_continuous_f : ∃ f : ℝ → ℝ, (∀ x, Tendsto (λ y => f (x + y) - f (x - y)) (𝓝[≠] 0) (𝓝 0)) ∧ ¬ Continuous f :=
sorry

theorem closure_of_zero_set {α : Type*} [MetricSpace α] {f : α → ℝ}
  (hf : Continuous f) :
  IsClosed {x | f x = 0} :=
sorry

theorem
  {α : Type} [MetricSpace α]
  {β : Type} [MetricSpace β]
  (f g : α → β)
  (s : Set α)
  (h₁ : Continuous f)
  (h₂ : Continuous g)
  (h₃ : Dense s)
  (h₄ : ∀ x ∈ s, f x = g x) :
  f = g :=
sorry

theorem exists_set_f : ∃ (E : Set ℝ) (f : ℝ → ℝ), ContinuousOn f E ∧ ¬∃ g : ℝ → ℝ, Continuous g ∧ ∀ x ∈ E, f x = g x :=
sorry

theorem UniformContinuousOn (f : ℝ → ℝ) (E : Set ℝ)
  (hE : Bornology.IsBounded E) (hf : UniformContinuousOn f E) :
  Bornology.IsBounded (Set.image f E) :=
sorry

theorem UniformContinuousMap {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  (f : X → Y) (hf : UniformContinuous f) :
  ∀ (x : ℕ → X), CauchySeq x → CauchySeq (λ n => f (x n)) :=
sorry

theorem monotononeContinuousOpenMap {f : ℝ → ℝ} (hf : Continuous f)
  (hopen : IsOpenMap f) : Monotone f :=
sorry

theorem
  (X : Type*) [MetricSpace X]
  (K F : Set X)
  (hK : IsCompact K)
  (hF : IsClosed F)
  (hKF : Disjoint K F) :
  ∃ δ > 0, ∀ p ∈ K, ∀ q ∈ F, dist p q ≥ δ :=
sorry

theorem formalization_98765 {f : ℝ → ℝ} (hf : ∀ x y, |f x - f y| ≤ (x - y)^2) :
    ∃ c, f = λ x => c :=
sorry

theorem formalization_98762 {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
  (M : ℝ) (hM : ∀ x, |deriv g x| ≤ M) :
  ∃ N, ∀ ε > 0, ε < N → Function.Injective (λ x => x + ε * g x) :=
sorry

theorem Tendsto_diff_f_prime_to_0
  {f : ℝ → ℝ}
  (hf : DifferentiableOn ℝ f (Set.Ioi 0))
  (hfn : Tendsto (deriv f) atTop (𝓝 0)) :
  Tendsto (λ x => f (x + 1) - f x) atTop (𝓝 0) :=
sorry

theorem Tendsto_ratio (f g : ℝ → ℝ) (x : ℝ)
  (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
  (hfn0 : deriv g x ≠ 0) (hf0 : f x = 0) (hg0 : g x = 0) :
  Tendsto (λ t => f t / g t) (𝓝 x) (𝓝 (deriv f x / deriv g x)) :=
sorry

theorem iteratedDeriv_eval (f : ℝ → ℝ)
    (hf : DifferentiableOn ℝ f (Set.Icc (-1) 1))
    (hfn : DifferentiableOn ℝ (deriv f) (Set.Icc (-1) 1))
    (hfn' : DifferentiableOn ℝ (deriv (deriv f)) (Set.Icc (-1) 1))
    (hf1 : f (-1) = 0)
    (hf2 : f 0 = 0)
    (hf3 : f 1 = 1)
    (hf4 : deriv f 0 = 0) :
    ∃ x ∈ Set.Ioo (-1) 1, iteratedDeriv 3 f x ≥ 3 := by sorry

theorem no_topology_needed :
  ¬ (∀ X : Type, ∀ U : Set X, Infinite U ∨ U = ∅ ∨ U = ⊤ → IsOpen U) :=
sorry

theorem
  : ∃ (X : Type*) (T : ℕ → Set (Set X)), (∀ i, IsTopologicalSpace (T i)) ∧ ¬IsTopologicalSpace (⋂ i, T i) :=
sorry

theorem generateFrom (X I : Type*) [TopologicalSpace X] (T : I → Set (Set X)) :
    ∃! T', IsGreatest {T' | ∀ i, T' ⊆ T i} ∧
    (∀ i, T' ⊆ T i) ∧
    (∀ T'', (∀ i, T'' ⊆ T i) → T' ⊆ T'') :=
sorry

theorem generateFrom {X : Type*} [TopologicalSpace X]
  (A : Set (Set X)) (hA : IsTopologicalBasis A) :
  generateFrom A = generateFrom (⋂ (T : Set (Set X)), if T ⊆ A then T else ⊥) :=
sorry

theorem generateFrom (S : Set (Set ℝ)) :
  IsTopologicalBasis S ↔
  (∀ T ∈ S, ∃ a b : ℚ, a < b ∧ T = {x | a < x ∧ x < b}) ∧
  (∀ U : Set ℝ, IsOpen U → ∃ T ∈ S, T ⊆ U) ∧
  (∀ U ∈ S, IsOpen U) ∧
  (∀ T ∈ S, T ≠ ∅) := by sorry

theorem base_topology {X Y A : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] (hY : Y ≤ X) (hA : A ≤ Y) :
  A = (univ : Set A) :=
sorry

theorem formalization_487964 :
  IsTopologicalBasis {S : Set (ℝ × ℝ) | ∃ a b c d : ℚ, a < b ∧ c < d ∧ S = {(x, y) | a < x ∧ x < b ∧ c < y ∧ y < d}} :=
sorry

theorem order_topology {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [LinearOrder Y] [OrderTopology Y] {f g : X → Y}
  (hf : Continuous f) (hg : Continuous g) :
  IsClosed {x | f x ≤ g x} :=
sorry

theorem h : Continuous f ∧ T2Space Y → (∃! g : ℝ → Y, Continuous g ∧ ∀ x, g x = f x) :=
sorry

theorem metrizable : MetrizableSpace (ℝ × ℝ) :=
sorry

theorem noUniformConvergence :
  ¬ ∃ L, Tendsto (λ n => f n) atTop (𝓝 L) :=
sorry

theorem quotientMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) (hp : Continuous p)
  (h : ∃ f : Y → X, Continuous f ∧ p ∘ f = id) :
  IsQuotientMap p :=
sorry

theorem restrictOpenMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) (hp : IsOpenMap p) (A : Set X) (hA : IsOpen A) :
  IsOpenMap (p ∘ Subtype.val : A → Y) :=
sorry

theorem
    (X : Type*) [TopologicalSpace X]
    (A : ℕ → Set X)
    (hA : ∀ i, IsConnected (A i))
    (A₀ : Set X)
    (hA₀ : IsConnected A₀)
    (h : ∀ i, A₀ ∩ A i ≠ ∅) :
    IsConnected (A₀ ∪ (⋃ i, A i)) :=
sorry

theorem formalization_487964 {X : Type*} [TopologicalSpace X]
  (A : Set X) (C : Set X) (hC : IsOpen C) (hCA : C ⊆ A)
  (hCB : C ∩ (Aᶜ) ≠ ∅) :
  C ∩ (frontier A) ≠ ∅ :=
sorry

theorem quotient_topology {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) (hp : Function.Surjective p)
  (h : ∀ y, IsConnected (p ⁻¹' {y}))
  (h' : IsConnectedSpace Y) :
  IsConnectedSpace X :=
sorry

theorem fixed_point {f : ℝ → ℝ} (hf : Continuous f)
  (h : ∀ x ∈ Set.Icc 0 1, f x ∈ Set.Icc 0 1) :
  ∃ x ∈ Set.Icc 0 1, f x = x :=
sorry

theorem component_of_group {G : Type*} [TopologicalSpace G] [Group G]
  (C : Set G) (hC : C = {x | ∃ y, x * y = 1}) :
  IsNormalSubgroup C :=
sorry

theorem perfectMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) (h : Function.Surjective p) (hc : Continuous p)
  (hp : ∀ y, IsCompact (p ⁻¹' {y})) :
  CompactSpace X :=
sorry

theorem countably_compact_iff_limit_point_compact {X : Type*} [TopologicalSpace X]
  (hT1 : T1Space X) :
  countably_compact X ↔ limit_point_compact X :=
sorry

theorem isometric_homeomorphism {X : Type*} [MetricSpace X] [CompactSpace X]
  (f : X → X) (h : Isometry f) :
  Function.Bijective f ∧ ∃ h : X → X, Continuous h ∧ ∀ x, f x = h x :=
sorry

theorem nonlocally_compact : ¬ LocallyCompactSpace (Set.Icc 0 1) :=
sorry

theorem countable_product_of_countable_dense_set {X : ℕ → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, ∃ (s : Set (X i)), Countable s ∧ Dense s) :
  ∃ (s : Set (Π i, X i)), Countable s ∧ Dense s :=
sorry

theorem regular_space {X : Type*} [TopologicalSpace X]
  (h : RegularSpace X) (x y : X) :
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧ closure U ∩ closure V = ∅ :=
sorry

theorem order_topology_regular {X : Type*} [TopologicalSpace X] [OrderTopology X] :
    RegularSpace X :=
sorry

theorem prod_hausdorff {α : Type*} [TopologicalSpace α]
  (X : α → Type*) [∀ i, TopologicalSpace (X i)] (hX : ∀ i, Nonempty (X i))
  (h : T2Space (Π i, X i)) :
  ∀ i, T2Space (X i) :=
sorry

theorem prod_normal {ι : Type*} {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)] (h : ∀ i, Nonempty (X i))
  (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) :=
sorry

theorem LocallyCompactHausdorffSpace.IsRegular (X : Type*) [TopologicalSpace X]
  [LocallyCompactSpace X] [T2Space X] :
  ∀ x A, IsClosed A → ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ A :=
sorry

theorem metrizable_compact_hausdorff {X : Type*} [CompactSpace X] [T2Space X]
  (X1 X2 : Set X) (hX1 : IsClosed X1) (hX2 : IsClosed X2)
  (hX : X1 ∪ X2 = univ) (hX1m : MetrizableSpace X1)
  (hX2m : MetrizableSpace X2) :
  MetrizableSpace X :=
sorry

theorem
    (X : Type*) [MetricSpace X]
    (Y : Type*) [MetricSpace Y]
    (hY : CompleteSpace Y)
    (A : Set X)
    (f : X → Y)
    (hf : UniformContinuousOn f A)
    : ∃! g : X → Y, ContinuousOn g (closure A) ∧ UniformContinuousOn g (closure A) :=
sorry

theorem cbrt_1 : ((-1 : ℂ) + Real.sqrt 3 * .I) / 2 ^ 3 = 1 :=
sorry

theorem algebra_498724 {F V : Type*} [AddCommGroup F] [AddCommGroup V]
  [Module F V] (a v : F) (h : a • v = 0) :
  a = 0 ∨ v = 0 :=
sorry

theorem example_nonempty_U : ∃ U : Set (ℝ × ℝ), Nonempty U ∧ (∀ x ∈ U, ∀ c : ℝ, c • x ∈ U) ∧ ¬∃ L : Submodule ℝ (ℝ × ℝ), U = ↑L :=
sorry

theorem union_of_submodule (F V : Type*) [AddCommGroup V] [Field F]
  [Module F V] (U W : Submodule F V) :
  ∃ U' : Submodule F V, U' = ↑U ∪ ↑W ↔ (U ≤ W ∨ W ≤ U) :=
sorry

theorem linearMapToModuleHom {F V W : Type*} [AddCommGroup V] [AddCommGroup W]
  [Field F] [Module F V] [Module F W] (T : V →ₗ[F] W) :
  ∃ U : Submodule F V, U ⊓ (range T) = ⊥ ∧
  ∀ x : V, T x ∈ range T ↔ x ∈ U :=
sorry

theorem sum_of_invariant_submodule {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {n : ℕ} (hn : 0 < n) (T : End F V)
  (U : Fin n → Submodule F V) (hU : ∀ i, Submodule.map T (U i) = U i) :
  Submodule.map T (∑ i : Fin n, U i) = ∑ i : Fin n, U i :=
sorry

theorem lmul_comm {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {S T : End F V} :
  (S * T).Eigenvalues = (T * S).Eigenvalues :=
sorry

theorem linearMap_invariant {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {T : End F V}
  (hS : ∀ U : Submodule F V, finrank F U = finrank F V - 1 →
    Submodule.map T U = U) :
  ∃ c : F, T = c • LinearMap.id :=
sorry

theorem formalization_98768 {V : Type*} [AddCommGroup V] [Module ℝ V]
  [FiniteDimensional ℝ V] (T : End ℝ V) (hT : ∀ c, eigenspace T c = ⊥) :
  ∀ U : Submodule ℝ V, U.map T = U → Even (finrank U) :=
sorry

theorem sum_of_products {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ) :
    (∑ i : Fin n, a i * b i) ^ 2 ≤ (∑ i : Fin n, i * a i ^ 2) * (∑ i : Fin n, b i ^ 2 / i) :=
sorry

theorem norm_eq_sum_of_squares {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] (e : ℕ → V) (he : ∀ i j, i ≠ j → e i ≠ 0)
  (horthogonal : ∀ i j, i ≠ j → inner (e i) (e j) = 0) :
  ∀ v : V, ‖v‖^2 = ∑ i : Fin m, ‖inner v (e i)‖^2 ↔
  v ∈ span ({e i | i : Fin m}) :=
sorry

theorem dim_ge_2_not_normal_subspace {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] (hV : finrank V ≥ 2) :
  ¬ ∃ U : Submodule ℝ (End ℝ V), ∀ T ∈ U, IsNormal T :=
sorry

theorem prove_478984 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] (T : End ℂ V)
  (hT : T * adjoint T = adjoint T * T) :
  (∀ e ∈ T.Eigenvalues, ∃ r : ℝ, e = r) ↔
  (∀ v : V, ∃ w : V, T v = w ∧ adjoint T v = w) :=
sorry

theorem inner_product_space_square_root {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] {T : End ℂ V}
  (hT : T*adjoint T = adjoint T*T) :
  ∃ S : End ℂ V, S^2 = T :=
sorry

theorem sum_not_integer (n : ℕ) :
    ¬ ∃ m : ℤ, ∑ i in range n, (1 / (i + 1)) = m := sorry

theorem number_theory_98765 {a m n : ℕ} (ha : a ≠ 0)
  (hm : m > 0) (hn : n > 0) :
  (Odd a → Nat.Coprime (a^(2^n) + 1) (a^(2^m) + 1)) ∧
  (Even a → 2 ∣ Nat.gcd (a^(2^n) + 1) (a^(2^m) + 1)) := by sorry

theorem sumsqfree : ¬ Summable (λ n => (1 : ℝ)/n) :=
sorry

theorem no_solution : ¬ ∃ x y : ℤ, 3 * x ^ 2 + 2 = y ^ 2 :=
sorry

theorem factorial_not_prime {n : ℕ} (hn : ¬ Nat.Prime n) :
    n ≠ 4 → ((Nat.factorial (n - 1)) % n = 0) := by sorry

theorem isPrimitiveRoot (p a : ℕ) [inst : Fact (Nat.Prime p)] :
    IsPrimitiveRoot a p ↔ IsPrimitiveRoot (-a : ZMod p) p :=
sorry

theorem is_fermat_prime (p n : ℕ) (hp : p = 2 ^ n + 1) :
    IsCyclic (ZMod p)ˣ → 3 ∈ (ZMod p)ˣ :=
sorry

theorem sum_of_powers (p k : ℕ) (hp : Nat.Prime p) :
    (∑ i in range p, (i + 1)^k) ≡ if p - 1 ∣ k then 0 [ZMOD p] else 0 [ZMOD p] := by sorry

theorem formalization_487964 {p : ℕ} (hp : p ≡ 1 [MOD 4]) :
    ∃ x, x^4 ≡ 2 [MOD p] ↔ ∃ A B, p = A^2 + 64 * B^2 := by sorry

theorem algebraic_number : IsAlgebraic ℚ (Real.sin (π/12)) :=
sorry

theorem f_447301 {f : ℂ → ℂ} (Ω : Set ℂ) (a b : Ω) (h : IsOpen Ω)
  (hf : DifferentiableOn ℂ f Ω) (hc : ∃ c, ∀ z ∈ Ω, (f z).im = c) :
  f a = f b :=
sorry

theorem no_convergence (z : ℂ) (hz : abs z = 1) :
    ¬ Summable (λ n => n * z ^ n) :=
sorry

theorem sum_series (f : ℂ → ℂ) (hf : f = λ z => ∑' n : ℕ, z * n / n)
    (z : ℂ) (hz : abs z = 1) (hz1 : z ≠ 1) :
    ∃ y, Tendsto (λ t => f z) atTop (𝓝 y) :=
sorry

theorem taylor_series : ∫ x in Set.Ioi 0, Real.sin x / x = Real.pi / 2 := by sorry

theorem formalization
  {f : ℂ → ℂ}
  (hf : Differentiable ℂ f)
  (h : ∀ z₀ : ℂ, ∃ n : ℕ, (f z₀).coeff n = 0)
  : ∃ p : ℂ[X], ∀ z : ℂ, f z = p.eval z :=
sorry

theorem tue_97828 (a : ℝ) (ha : 0 < a) :
    Tendsto (λ y => ∫ x in -y..y, x * Real.sin x / (x ^ 2 + a ^ 2)) atTop (𝓝 (Real.pi * (Real.exp (-a)))) :=
sorry

theorem formalization_of_978324
  (f : ℂ → ℂ)
  (hf : Differentiable ℂ f)
  (hinjective : Function.Injective f) :
  ∃ a b, ∀ z, f z = a * z + b ∧ a ≠ 0 :=
sorry

theorem sum_of_residuals (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (ball 0 1))
(hfb : Bornology.IsBounded (Set.range f)) (hfnz : f ≠ 0)
(z : ℕ → ℂ) (hz : ∀ k, f (z k) = 0) (hz1 : ∀ k, ‖z k‖ < 1) :
∃ y, Tendsto (λ n => ∑ i in range n, (1 - ‖z i‖)) atTop (𝓝 y) :=
sorry

theorem formalization_978844
  (f : ℝ → ℝ)
  (h₀ : Differentiable ℝ f)
  (h₁ : ∀ x, iteratedDeriv x f x ≥ 0)
  (h₂ : f 0 = 0)
  (h₃ : f 1 = 1) :
  ∃ n > 0, ∃ x, iteratedDeriv n f x < 0 :=
sorry

theorem seq_periodic {a : ℝ} (x : ℕ → ℝ)
  (hx0 : x 0 = 1)
  (hx1 : x 1 = a)
  (hxn : ∀ n ≥ 2, x (n + 1) = 2 * (x n) * (x (n - 1)) - x (n - 2))
  (h : ∃ n, x n = 0) :
  ∃ c, Function.Periodic x c :=
sorry

theorem infinite_primes : ∀ n, ∃ p, n < p ∧ Nat.Prime p := sorry

theorem unique_a_n :
  ∃! a : ℕ, ∃! n : ℕ, 0 < a ∧ 0 < n ∧ a^(n + 1) - (a + 1)^n = 2001 :=
sorry

theorem iteratedDeriv_4
  (f : ℝ → ℝ)
  (h₀ : ContDiff ℝ 3 f)
  (h₁ : ∀ x, 0 < f x)
  (h₂ : ∀ x, 0 < deriv f x)
  (h₃ : ∀ x, 0 < iteratedDeriv 2 f x)
  (h₄ : ∀ x, 0 < iteratedDeriv 3 f x)
  (h₅ : ∀ x, iteratedDeriv 3 f x ≤ f x) :
  ∀ x, deriv f x < 2 * f x :=
sorry

theorem formalization (a b c : ℤ) :
    ∃ n : ℕ, 0 < n ∧ ¬ ∃ m : ℤ, m^2 = n^3 + a * n^2 + b * n + c := by sorry

theorem isOpen {M : Type*} [TopologicalSpace M] (U : Set M) :
    IsOpen U ↔ ∀ x ∈ U, ¬ ClusterPt x (𝓟 Uᶜ) :=
sorry

theorem isClopen (s : Set ℕ) : Prop :=
sorry

theorem
    {M : Type*} [MetricSpace M]
    (A B : Set M)
    (hA : IsCompact A)
    (hB : IsCompact B)
    (hAB : Disjoint A B)
    (hA_ne_empty : A ≠ ∅)
    (hB_ne_empty : B ≠ ∅) :
    ∃ a₀ ∈ A, ∃ b₀ ∈ B, ∀ a ∈ A, ∀ b ∈ B, dist a₀ b₀ ≤ dist a b :=
sorry

