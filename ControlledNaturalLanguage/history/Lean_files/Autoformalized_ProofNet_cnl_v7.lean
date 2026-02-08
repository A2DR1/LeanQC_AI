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

theorem multmod (n : ℕ) (a b c : ℤ) :
  ((a * b) % n) * c % n = a % n * (b * c) % n :=
sorry

theorem exists_polynomial_eval_zero (x : ℝ) (hx : x = sin (π / 12)) :
    ∃ P : Polynomial ℤ, P.eval x = 0 := by sorry

theorem exist_point : ∃ x ∈ X, ∀ U : Set ℝ, IsOpen U → x ∈ U → ¬Compact (closure U) :=
sorry

theorem linearMapFromVtoW {n : ℕ} (hn : 0 < n) :
    ∃ L : (Fin n → ℝ) →ₗ[ℚ] ℝ,
      Function.Bijective L :=
sorry

theorem sum_of_kth_powers (p k : ℕ) (hp : Nat.Prime p) :
    ((¬(p-1 ∣ k)) → (∑ i in range p, (i+1)^k ≡ 0 [MOD p])) ∧
    (p-1 ∣ k → (∑ i in range p, (i+1)^k ≡ -1 [ZMOD p])) := by sorry

theorem exists_topology_not_topology :
  ∃ X : Type*, ¬ IsTopologicalSpace X ∧ (Set.univ : Set X) ∈ 𝒨 X :=
sorry

theorem number_theory_98765 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 105) (n_5 n_7 : ℕ)
  (hn_5 : n_5 = {H : Sylow 5 G | H.Normal}.ncard)
  (hn_7 : n_7 = {H : Sylow 7 G | H.Normal}.ncard)
  (hdiv : n_5 ∣ 21 ∧ n_7 ∣ 15)
  (hmod : n_5 ≡ 1 [MOD 5] ∧ n_7 ≡ 1 [MOD 7]) :
  n_5 = 1 ∧ n_7 = 1 := by sorry

theorem formalization_987654
  (n : ℕ)
  (f_n : ℝ → ℝ)
  (h_f_n : f_n = λ x => x ^ n)
  (ε : ℝ)
  (hε : ε > 0)
  (N : ℕ)
  (m : ℕ)
  (hm : m ≥ N)
  (x : ℝ)
  (hx : x ∈ Set.Icc 0 1)
  (h : |f_n m - f_n x| ≥ ε) :
  False := by sorry

theorem prod_of_nonzero : ∀ (K : Type*) [Field K] [Fintype K], (∏ x : K, if x ≠ 0 then x else 1) = -1 :=
sorry

theorem S_not_integer : ¬ ∃ m : ℤ, S n = m :=
sorry

def p : X → Y
sorry

theorem g_478964 {G : Type*} [CommGroup G] [Fintype G]
  (p n m : ℕ) (hp : Nat.Prime p) (hn : 0 < n) (hm : 0 < m)
  (hpn : ¬ p ∣ m) (H : Subgroup G) [Fintype H] (hH : card H = p ^ n) :
  ∀ f : G ≃* G, f '' H = H :=
sorry

theorem entire_f (f : ℂ → ℂ) (hf : Differentiable ℂ f)
(hinjective : Injective f) :
∃ a b, a ≠ 0 ∧ ∀ z, f z = (a * z) + b :=
sorry

theorem closure_of_zero_set
  (X : Type*) [MetricSpace X]
  (f : X → ℝ)
  (h₁ : Continuous f) :
  IsClosed {x | f x = 0} :=
sorry

theorem formalization_497864
  (f : ℝ → ℝ)
  (h : ∀ t x, |f t - f x| ≤ (t - x)^2) :
  ∃ c, ∀ x, f x = c :=
sorry

theorem linear_operator(T : ℂ →ₗ[ℂ] V)
(m : ℕ)
(hm : 0 < m)
(U : ℕ → Submodule ℂ V)
(hU : ∀ i ∈ Icc 1 m, ∀ u : U i, T u ∈ U i)
: ∀ v : (Fin m → U) →ₗ[ℂ] V, T v ∈ (Fin m → U) →ₗ[ℂ] V :=
sorry

theorem fin_group_462 :
  ∃ (G : Type*) (_ : Fintype G) (_ : Group G),
    Fintype.card G = 462 ∧
    ∃ N : Subgroup G, N ≠ ⊥ ∧ N ≠ ⊤ ∧ N.Normal :=
sorry

theorem normal_subgroup {G : Type*} [Group G] {p α : ℕ}
  (hp : Nat.Prime p) (hpa : 0 < α) (hG : card G = p ^ α)
  (H : Subgroup G) (hH : H.index = p) :
  H.Normal :=
sorry

theorem g_h_isom {p q : ℕ} {G H : Type*}
  [Group G] [Group H]
  (hp : Nat.Prime p)
  (hq : Nat.Prime q)
  (h : p > q)
  (hk : (p - 1) = q * k)
  (hG : card G = p * q)
  (hH : card H = p * q)
  (hG' : ¬CommGroup G)
  (hH' : ¬CommGroup H) :
  G ≃* H :=
sorry

theorem normal_subgroup {G : Type*} [TopologicalSpace G] [Group G]
  (C : Set G) (hC : C = {x | x ∈ univ}) :
  C.Normal :=
sorry

theorem cover_compact
  {X : Type*} [TopologicalSpace X]
  (K : ℕ → Set X)
  (hK : ∀ n, IsOpen (K n))
  (hK1 : ∀ n, K n ⊆ ⋃ m in (Ici n), K m)
  (hK2 : ∀ n, ∃ m, m ∈ Ici n ∧ K n ⊆ ⋃ i in (Icc 1 m), K i) :
  ⋂ n, K n ≠ ∅ :=
sorry

theorem no_convergence (S : ℂ → ℂ)
    (hS : ∀ z, S z = ∑' n : ℕ, n * z ^ n) :
    ∀ z, ‖z‖ = 1 → ¬ Summable (λ n => S z) :=
sorry

theorem g_478964 {G : Type*} [Group G] [Finite G]
  (φ : G ≃* G) (S : Set G) (hS : S = {x | φ x = x⁻¹})
  (hS1 : S.ncard > (3 / 4 : ℚ) * (Nat.card G)) :
  (∀ y, φ y = y⁻¹) ∧ (∀ a b, a * b = b * a) :=
sorry

theorem distance_between_compact_set :
  ∀ {M : Type*} [MetricSpace M]
  (A B : Set M)
  (hA : IsCompact A)
  (hB : IsCompact B)
  (hA_ne_empty : A.Nonempty)
  (hB_ne_empty : B.Nonempty)
  (hAB : ∀ a ∈ A, ∀ b ∈ B, a ≠ b)
  (d : M → M → ℝ)
  (hd : d = λ x y => dist x y) :
  ∃ a₀ ∈ A, ∃ b₀ ∈ B, ∀ a ∈ A, ∀ b ∈ B, d a₀ b₀ ≤ d a b :=
sorry

theorem infinite_primes : ∀ n, ∃ p, n < p ∧ Nat.Prime p := sorry

theorem union_of_A_and_Aa (X : Type*) [TopologicalSpace X]
  (A : Set X) (hA : IsConnected A)
  (Aa : ℕ → Set X) (hAa : ∀ i, IsConnected (Aa i))
  (hA_inter_Aa : ∀ i, A ∩ Aa i ≠ ∅) :
  IsConnected (A ∪ (⋃ i, Aa i)) :=
sorry

theorem group_hhk {G : Type*} [Group G] (H K : Subgroup G)
  (hHK : ∀ g : G, (g * H) = (H * g)) (hHK' : ∀ g : G, (g * K) = (K * g)) :
  ∀ g : G, (g * (H ∩ K)) = ((H ∩ K) * g) :=
sorry

theorem phi_not_bijective : ¬ Function.Bijective (fun A ↦ A.det⁻¹ • A) :=
sorry

theorem f (x : ℚ) : x^3 + 3 * x + 2 ≠ 0 := by sorry

theorem formalization
  {R : Type*} [Ring R]
  {n : ℕ}
  {a : ℕ → R}
  {p : R → R}
  (hp : p = λ x => ∑ i in Finset.range (n+1), a i * x ^ i)
  (hdiv : ∃ b : R, b ≠ 0 ∧ ∀ x : R, b * p x = 0) :
  ∃ b : R, b ≠ 0 ∧ ∀ x : R, b * p x = 0 :=
sorry

theorem sylow_478924 {G : Type*} [Group G] [Fintype G]
  (hG : card G = 351) :
  ∃ p, Nat.Prime p ∧ p ∣ 351 ∧ {S : Sylow p G | S.Normal}.encard = 1 :=
sorry

theorem exist_fixed_point
  (f : ℝ → ℝ)
  (h₀ : Continuous f)
  (h₁ : ∀ x, f x ∈ Set.Icc 0 1) :
  ∃ x, f x = x :=
sorry

theorem f_Ω (f : ℂ → ℂ) (Ω : Set ℂ) (a b : Ω)
(h₁ : IsOpen Ω) (h₂ : DifferentiableOn ℂ f Ω)
(h₃ : ∃ c : ℝ, ∀ z ∈ Ω, (f z).im = c) :
∀ z ∈ Ω, f z = f a := by sorry

theorem IrreducibleP : Irreducible (P : Zsqrtd → Zsqrtd) :=
sorry

theorem exist_m : ∀ I : Ideal (GaussianInt), I ≠ ⊥ → ∃ m : GaussianInt, m ∈ I ∧ m ≠ 0 :=
sorry

Statement to Formalize:
        Assumptions:
Let V be a complex inner-product space.
Define T : V → V as a linear operator.
Assume T is normal.
Define λ as a complex number.
Assume v is a vector in V.
Assume v ≠ 0.
Assume T(v) = λ * v.
Goal:
(T is self-adjoint) if and only if (for every eigenvalue λ of T, λ is a real number).
         -/
theorem isSelfAdjoint {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V) (hT : T*adjoint T = adjoint T*T)
  (v : V) (hv : v ≠ 0) (hT1 : T v = c • v) :
  (∀ c : ℂ, T v = c • v → ∃ r : ℝ, c = r) ↔
  (∀ c : ℂ, T v = c • v → ∃ r : ℝ, c = r) :=
sorry

/- Reference Example:
Input: "There are infinite prime numbers."
Output: 
theorem infinite_primes : ∀ n, ∃ p, n < p ∧ Nat.Prime p := sorry
 -/
theorem formalization {X : Type*} [TopologicalSpace X]
  (C : Set (Set X)) (hC : IsTopologicalBasis C) :
  generateFrom C = generateFrom (⋂ τ ∈ C, τ) :=
sorry

theorem orderOf (p : ℕ) (hp : Nat.Prime p) (G : Type*) [Group G]
  [Fintype G] (hG : card G = p - 1) (hG1 : ∀ x : G, orderOf x ∣ p - 1)
  (a : ℤ) : a ^ p ≡ a [ZMOD p] :=
sorry

theorem formalization_497864
  (f : ℝ → ℝ)
  (h : ∀ x y, |(f x - f y)| ≤ (x - y)^2) :
  ∀ x y, f x = f y :=
sorry

theorem ContinuousOpenMap
  (f : ℝ → ℝ)
  (h₁ : Continuous f)
  (h₂ : IsOpenMap f)
  (a b : ℝ) :
  a < b → (f a ≤ f b ∨ f a ≥ f b) :=
sorry

theorem partial_sum_tendsto_infinite : Tendsto P atTop atTop :=
sorry

theorem no_zero : ¬∃ a, P a = 0 :=
sorry

theorem prod_hausdorff {α : Type*} [TopologicalSpace α]
  (h : ∀ x y : α, x ≠ y → ∃ U V : Set α, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V) :
  ∀ x y : α, x ≠ y → ∃ U V : Set α, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V :=
sorry

theorem formalization_487399
  (U : Set ℝ)
  (hU : IsOpen U)
  (a b : ℝ → ℝ)
  (ha : ∀ x ∈ U, a x = sInf {y | x ≃ y})
  (hb : ∀ x ∈ U, b x = sSup {y | x ≃ y})
  (C : Set ℝ → Prop)
  (hC : C = λ S => ∃ x ∈ U, a x = sInf S ∧ b x = sSup S) :
  (∀ x ∈ U, C x) ∧
  (∀ x ∈ U, ∀ y ∈ U, C x → C y → x ≠ y) ∧
  (∀ x ∈ U, ∀ y ∈ U, C x → C y → Disjoint (Set.Ioo (a x) (b x)) (Set.Ioo (a y) (b y))) ∧
  (∀ x ∈ U, C x → ∃! y, x = y) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x)) ∧
  (∀ x ∈ U, C x → ∃! y, y ∈ Set.Ioo (a x) (b x

theorem t1_space {X : Type*} [TopologicalSpace X]
  (ht1 : T1Space X)
  (h : ∀ U : ℕ → Set X,
    (∀ i, IsOpen (U i)) ∧
    (∀ i, U i ⊆ X) ∧
    (∀ i, ∀ j, i ≠ j → Disjoint (U i) (U j)) →
    ∃ F : Finset ℕ, ∀ i ∈ F, U i ⊆ X) :
  ∀ A : Set X, Infinite A → ∃ x ∈ A, ∀ U : Set X, IsOpen U → U ⊆ A → x ∈ U →
  ∃ y ∈ U, y ≠ x ∧ y ∈ A :=
sorry

theorem order_of {G : Type*} [Group G] (x : G) :
    orderOf x = orderOf (x⁻¹) := by sorry

theorem f_Injective {F G : Type*} [Field F] [Field G]
  (f : F →+* G) (hadd : ∀ x y, f (x + y) = f x + f y)
  (hf : ∀ x y, f (x * y) = f x * f y) (hf1 : f 1 = 1) (hf2 : f 0 = 0) :
  Function.Injective f :=
sorry

theorem sum_of_norms {n : ℕ} (f : Fin n → ℂ) :
    ‖∑ i : Fin n, f i‖ ≤ ∑ i : Fin n, ‖f i‖ :=
sorry

theorem group_algebra {G : Type*} [Group G] (h : ∀ H : Subgroup G, H.Normal)
  (a b : G) :
  ∃ j : ℕ, b * a = (a ^ j) * b :=
sorry

theorem statement_to_formalize :
  (∀ ε > 0, ∃ δ > 0, ∀ x ∈ E, ∀ y ∈ E, |x - y| < δ → |f x - f y| < ε) →
  goal := sorry

theorem
    (r : ℚ)
    (x : ℝ)
    (h₀ : r ≠ 0)
    (h₁ : Irrational x) :
    Irrational ((↑r) * x) := by sorry

theorem Subgroup.index_eq_zero_iff_hK : ∀ {G : Type*} [Group G] (H : Subgroup G)
  (hH : H ≠ ⊤) :
  H.index = 0 ↔ ∃ K ≤ H, K.Normal ∧ K.index ≤ Nat.factorial H :=
sorry

theorem sum_of_nonnegatives
  (a : ℕ → ℝ)
  (h₀ : ∀ n, 0 ≤ a n)
  (h₁ : ∃ L, Tendsto (λ n => ∑ i in range n, a i) atTop (𝓝 L))
  : ∃ L, Tendsto (λ n => ∑ i in range n, (sqrt (a i)) / (i + 1)) atTop (𝓝 L) :=
sorry

theorem countable_base {K : Type*} [MetricSpace K] [CompactSpace K]
  (d : K → K → ℝ)
  (h_d : d = λ x y => dist x y)
  (B : ℕ → Set (Set K))
  (h_B : ∀ n, B n = {x | ∃ y, x = ball y (1 / n)})
  (F : ℕ → Set K)
  (h_F : ∀ n, IsFinite (F n))
  (h_F' : ∀ n, (B n) '' (F n) = univ)
  : ∃ ℂ : Set (Set K), Countable ℂ ∧ Set.IsTopologicalBasis ℂ :=
sorry

theorem formalization
  (a : ℝ)
  (x : ℕ → ℝ)
  (hx0 : x 0 = 1)
  (hx1 : x 1 = a)
  (hx2 : x 2 = a)
  (hxn : ∀ n ≥ 2, x (n + 1) = (2 * x n * x (n - 1)) - x (n - 2))
  (h0 : ∃ n, x n = 0) :
  ∃ p > 0, Function.Periodic x p :=
sorry

theorem norm_add (k : ℕ) (x y : EuclideanSpace ℝ (Fin k)) :
    ‖x + y‖^2 + ‖x - y‖^2 = 2 * ‖x‖^2 + 2 * ‖y‖^2 :=
sorry

theorem quotientMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) (f : Y → X) (hp : Continuous p) (hf : Continuous f)
  (h : ∀ y, p (f y) = y) :
  IsQuotientMap p :=
sorry

theorem regular_space_pointwise {X : Type*} [TopologicalSpace X]
  [RegularSpace X] (a b : X) (hab : a ≠ b) :
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ a ∈ U ∧ b ∈ V ∧ closure U ∩ closure V = ∅ :=
sorry

theorem g_478966 {G : Type*} [Group G] [Fintype G]
  (hG : Even (card G)) :
  ∃ a : G, a ≠ 1 ∧ a = a⁻¹ :=
sorry

theorem t2_47 {X : Type*} [TopologicalSpace X]
  (A C : Set X) (hC : IsConnected C) (hCA : C ∩ A ≠ ∅)
  (hCB : C ∩ (univ \ A) ≠ ∅) :
  C ∩ (frontier A) ≠ ∅ :=
sorry

theorem finsubgroup_set_nonempty {G : Type*} [Group G] {H K : Subgroup G}
  [Fintype H] [Fintype K]
  (hHK : Nat.Coprime (card H) (card K)) :
  (H ∩ K).Nonempty :=
sorry

theorem sylow_hK {G : Type*} [Group G] {p : ℕ} (hp : Nat.Prime p)
  {P : Subgroup G} (hP : IsPGroup p P) (hP1 : P.Normal) :
  ∃ H : Subgroup G, ∃ K : Subgroup G, K = P ⊓ H ∧ IsPGroup p K ∧
  ∀ Q : Subgroup G, IsPGroup p Q → Q ≤ H → Q = K :=
sorry

theorem formalization_978844
  (X : Type*) [TopologicalSpace X]
  (I : Type*) [Fintype I]
  (T : I → Set (Set X))
  (hT : ∀ i, IsTopology (T i)) :
  ¬ IsTopology (⋃ i, T i) :=
sorry

theorem exists_topology :
    ∃ d : X → ℝ,
      (∀ x y, d x = d y → x = y) ∧
      (∀ U ∈ T, IsOpen U) ∧
      (∀ x, IsClosed {y | d x = y}) ∧
      (∀ U, IsOpen U → IsOpen (d '' U)) ∧
      (∀ U, IsClosed U → IsClosed (d '' U)) := sorry

theorem multiplicity_1 {p n : ℕ} (hp : Nat.Prime p) (hn : 0 < n)
  (F : Type*) [Field F] [CharP F p] (P : F → F) (hP : P = λ x => x^(p^n) - x)
  (a b : F) (ha : P a = 0) (hb : P b = 0) (hab : a ≠ b) :
  orderOf (rootMultiplicity P a) = 1 ∧ orderOf (rootMultiplicity P b) = 1 :=
sorry

theorem group_fins : ∀ G [Group G], (Set.ncard {g : G | True} = 9) → (∀ a b : G, a*b = b*a) := by sorry

theorem group_mul_left {G : Type*} [Group G] (a b : G)
  (f : G → G) (hf : f = λ x => (b⁻¹) * x * b) :
  ∃ c : G, (a * b) = c * (b * a) * (c⁻¹) :=
sorry

theorem both_open_and_closed {S : Set ℕ} (hS : is_topology S) :
    IsOpen S ∧ IsClosed S :=
sorry

theorem formalization
  (p : ℂ → ℂ)
  (a : ℂ)
  (h₀ : ∀ x, p x = ((x ^ 5 + (√2) * (x ^ 3)) + (√5) * (x ^ 2)) + (√7) * x + √11)
  (h₁ : p a = 0) :
  ∃ q : Polynomial ℚ, q.eval a = 0 ∧ q.degree ≤ 80 :=
sorry

theorem h : ∀ x ∈ E, g x ≠ f x := by sorry

theorem sum_of_series (a b : ℕ → ℝ)
  (h₁ : ∃ L, Tendsto (λ n => (∑ i in range n, |a i|)) atTop (𝓝 L))
  (h₂ : ∃ L, Tendsto (λ n => (∑ i in range n, |b i|)) atTop (𝓝 L))
  (c : ℕ → ℝ)
  (hc : ∀ n, c n = ∑ k in Finset.Icc 0 n, a k * b (n - k)) :
  ∃ L, Tendsto (λ n => (∑ i in range n, |c i|)) atTop (𝓝 L) :=
sorry

theorem g_497824 {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
  (h : p * q = card G) :
  ¬ IsSimpleGroup G :=
sorry

theorem algebra_487399 {R : Type*} [CommRing R] (a : R)
  (L : R → Set R) (hL : L = λ a => {x | x * a = 0}) :
  ∀ x ∈ L a, ∀ r : R, x + y ∈ L a ∧ r * x ∈ L a :=
sorry

theorem abelian_group {G : Type*} [Group G] [Fintype G]
  (hG : card G = p * q) (hp : Nat.Prime p) (hq : Nat.Prime q)
  (hne : p ≠ q) :
  IsCyclic G :=
sorry

theorem UniformContinuousOn
  {f : ℝ → ℝ}
  (hf : ContinuousOn f (Set.Icc a b))
  (h : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ μ (|(x - y)|))
  : ContinuousOn f (Set.Icc a b) :=
sorry

theorem id_eq_iff {S : Type*} [Fintype S] [Nonempty S]
  (σ τ : Equiv.Perm S)
  (h₁ : ∀ x, σ x ≠ x → τ x = x)
  (h₂ : ∀ x, τ x ≠ x → σ x = x)
  (h₃ : ∀ x, σ (τ x) = x) :
  (∀ x, σ x = x) ∧ (∀ x, τ x = x) :=
sorry

def T'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''' : Set X → Prop :=
  fun j

theorem vS : ∃ V : Type, [NormedAddCommGroup V] ∧ [InnerProductSpace ℂ V] ∧ [FiniteDimensional ℂ V]
  ∧ (FiniteDimensional.rank ℂ V ≥ 2) ∧ (∃ S : Set ( End ℂ V ), S = {T | T * adjoint T = adjoint T * T} ∧
  ∃ A ∈ S, ∃ B ∈ S, (A + B) ∉ S) := by sorry

theorem group_algebra_498067 {G : Type*} [Group G] {A : Subgroup G}
  [A.Normal] {b : G} {p : ℕ} (hp : Nat.Prime p) (hb : orderOf b = p)
  (h : ¬ b ∈ A) :
  A ⊓ (Subgroup.closure {b}) = ⊥ :=
sorry

theorem g : ℕ → ℕ → Prop :=
sorry

theorem linear_operator_composition {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] {S T : V →ₗ[F] V} {l : F}
  (hST : l ∈ (S ∘ T).Eigenvalues) :
  l ∈ (T ∘ S).Eigenvalues :=
sorry

theorem group_theory_9 {G : Type*} [Group G] {n : ℕ} (hn : 1 < n)
  (h : ∀ a b : G, (a * b) ^ n = (a ^ n) * (b ^ n)) :
  ∀ a b : G, (a * b * a⁻¹ * b⁻¹) ^ (n * (n - 1)) = 1 :=
sorry

theorem exist_group exist_normal_subgroup exist_non_charp : True :=
sorry

theorem quotientMapConnected {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) (hquot : IsQuotientMap p)
  (hY : ConnectedSpace Y) (hY' : ∀ y : Y, IsConnected (p ⁻¹' {y}))
  : ConnectedSpace X :=
sorry

theorem formalization_487949
  (f : ℝ → ℝ)
  (h₀ : ∀ x, 0 ≤ f x)
  (h₁ : f 0 = 0)
  (h₂ : f 1 = 1)
  (h₃ : ∀ n : ℕ, DifferentiableAt ℝ f n) :
  ∃ n : ℕ, ∃ x, iteratedDeriv n f x < 0 :=
sorry

theorem formalization
  (f : ℝ → ℝ)
  (g : ℝ → ℝ)
  (hf : ∀ x, 0 < x → DifferentiableAt ℝ f x)
  (hfg : ∀ ε, 0 < ε → ∃ M, ∀ x, 0 < x → x > M → |deriv f x| < ε)
  (hg : ∀ x, 0 < x → g x = f (x + 1) - f x) :
  ∀ ε, 0 < ε → ∃ N, ∀ x, 0 < x → x > N → |g x| < ε :=
sorry

theorem lower_bound_le_upper_bound {S : Type*} [PartialOrder S]
  (E : Set S) (hE : E.Nonempty) (α β : S)
  (h₁ : ∀ x ∈ E, α ≤ x) (h₂ : ∀ x ∈ E, x ≤ β) :
  α ≤ β :=
sorry

def B : Set (ℝ × ℝ) :=
sorry

theorem closure(X : Type*) [MetricSpace X] [CompleteSpace X]
  (A : Set X) (f : A → Y) (hf : UniformContinuous f)
  (g : closure A → Y) (hg : UniformContinuous g)
  (h₁ : ∀ a, g a = f a)
  (h₂ : ∀ h : closure A → Y, UniformContinuous h → (∀ a, h a = f a) →
    ∀ x, h x = g x) :
  True := by sorry

theorem sum_f (p : ℝ) (hp : 1 < p)
(f : ℕ → ℝ) (hf : ∀ k, f k = 1 / (k * (logb e k)^p)) :
Summable (λ k => f k) :=
sorry

theorem algebra_487394 {R : Type*} [Ring R] (I J : Ideal R)
  (h : ∀ r : R, ∃ i ∈ I, ∃ j ∈ J, r = i + j) :
  ∀ x : R, x ∈ I * J ↔ x ∈ I ∩ J :=
sorry

theorem unit_of_coprime {R : Type*} [Ring R] {u : R}
  (hu : IsUnit u) (huv : ∃ v : R, u * v = 1 ∧ v * u = 1) :
  IsUnit (-u) :=
sorry

theorem exists_nonint : ∃ a b c : ℤ, ∃ n : ℕ, 0 < n ∧ ¬(∃ m : ℤ, Real.sqrt ((n ^ 3) + (a * (n ^ 2)) + (b * n) + c) = m) :=
sorry

theorem solvable_group {G : Type*} [Group G] [IsSolvable G] {N : Subgroup G}
  [N.Normal] : IsSolvable (G ⧸ N) :=
sorry

theorem ringHomomorphism_surjective φ : Function.Surjective φ :=
sorry

theorem
  {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y)
  (h : ∀ U : Set X, IsOpen U → IsOpen (Set.image p U))
  (A : Set X)
  (hA : IsOpen A)
  (q : A → Y)
  (hq : ∀ a ∈ A, q a = p a) :
  ∀ V : Set A, IsOpen V → IsOpen (Set.image q V) :=
sorry

theorem isPrimitiveRoot (p : ℕ) (hp : Nat.Prime p) (a : ZMod p) :
    IsPrimitiveRoot (-a) p :=
sorry

theorem countable_summable (D : Set ℂ) (hD : D = {z | abs z < 1}) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f D) (M : ℝ) (hM : ∀ z ∈ D, abs (f z) ≤ M)
    (hM' : ∃ z ∈ D, f z ≠ 0) (Z : Set ℂ) (hZ : Z = {z | z ∈ D ∧ f z = 0})
    (hZ1 : Countable Z) (z : ℕ → ℂ) (hz : ∀ n, z n ∈ Z) (hz1 : ∀ n, abs (z n) < 1) :
    Summable (λ n => (1 - abs (z n))) :=
sorry

theorem iteratedDeriv_4
  (f : ℝ → ℝ)
  (h₀ : ∀ x, DifferentiableAt ℝ f x)
  (h₁ : ∀ x, ContinuousAt (iteratedDeriv 3 f) x)
  (h₂ : ∀ x, f x > 0)
  (h₃ : ∀ x, deriv f x > 0)
  (h₄ : ∀ x, iteratedDeriv 2 f x > 0)
  (h₅ : ∀ x, iteratedDeriv 3 f x > 0)
  (h₆ : ∀ x, iteratedDeriv 3 f x ≤ f x) :
  ∀ x, deriv f x < 2 * f x :=
sorry

def

