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

theorem A_positive (S : Finset (ℤ × ℤ)) (hS : S.Nonempty) : 0 < A S := sorry

theorem probability_intersection_bound (n : ℕ) (a : ℝ) (ha : a < 1/4) (A : ℕ → Set ℝ) 
(hprob : ∀ i ∈ Finset.range n, ProbabilityTheory.ProbMeasure.prob (A (i + 1)) ≥ 1 - a) 
(hindep : ∀ i j ∈ Finset.range n, |(i + 1 : ℤ) - (j + 1)| > 1 → ProbabilityTheory.Indep (A (i + 1)) (A (j + 1))) 
(u : ℕ → ℝ) (hu0 : u 0 = 1) (hu1 : u 1 = 1 - a) 
(hurec : ∀ k : ℕ, u (k + 2) = u (k + 1) - a * u k) 
(hupos : ∀ k ≤ n, u k > 0) : 
ProbabilityTheory.ProbMeasure.prob (⋂ i ∈ Finset.range n, A (i + 1)) ≥ u n := sorry

theorem lim_or_limsup (g : ℝ → ℝ) (hcont : ContinuousOn g (Icc 0 1)) (hdiff : ∀ᶠ x in 𝓝[>] (0 : ℝ), DifferentiableAt ℝ g x) (hdiff2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), DifferentiableAt ℝ (deriv g) x) (r : ℝ) (hr : r > 1) (hlim : Tendsto (fun x ↦ g x / x^r) (𝓝[>] 0) (𝓝 0)) : (Tendsto (deriv g) (𝓝[>] 0) (𝓝 0)) ∨ (Tendsto (fun x ↦ x^r * abs (deriv (deriv g) x)) (𝓝[>] 0) atTop) := sorry

theorem exists_periodic_divisibility : ∃ (n : ℕ), ∀ (m : ℕ), n ≤ m → m ≤ n + 2004 → 2006 ∣ x m := sorry

theorem subset_closed_under_mult_or {S : Set ℝ} (hS_mul : ∀ a b ∈ S, a * b ∈ S) (T U : Set S) 
(h_disj : Disjoint T U) (h_union : T ∪ U = S) 
(hT : ∀ a b c ∈ T, (a : ℝ) * b * c ∈ T) (hU : ∀ a b c ∈ U, (a : ℝ) * b * c ∈ U) : 
(∀ a b ∈ T, (a : ℝ) * b ∈ T) ∨ (∀ a b ∈ U, (a : ℝ) * b ∈ U) := sorry

theorem S_t_closed_under_multiplication_iff_t_le_one (t : ℝ) :
    (∀ (f g : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) → StrictMonoOn f (Set.Icc 0 1) → ConvexOn ℝ (Set.Icc 0 1) f →
    (∀ x ∈ Set.Icc 0 1, 0 ≤ f x) → f 1 - 2 * f (2/3) + f (1/3) ≥ t * (f (2/3) - 2 * f (1/3) + f 0) →
    ContinuousOn g (Set.Icc 0 1) → StrictMonoOn g (Set.Icc 0 1) → ConvexOn ℝ (Set.Icc 0 1) g →
    (∀ x ∈ Set.Icc 0 1, 0 ≤ g x) → g 1 - 2 * g (2/3) + g (1/3) ≥ t * (g (2/3) - 2 * g (1/3) + g 0) →
    ContinuousOn (f * g) (Set.Icc 0 1) ∧ StrictMonoOn (f * g) (Set.Icc 0 1) ∧ ConvexOn ℝ (Set.Icc 0 1) (f * g) ∧
    (∀ x ∈ Set.Icc 0 1, 0 ≤ (f * g) x) ∧ (f * g) 1 - 2 * (f * g) (2/3) + (f * g) (1/3) ≥ t * ((f * g) (2/3) - 2 * (f * g) (1/3) + (f * g) 0)) ↔ t ≤ 1 := sorry

theorem matrix_non_invertible (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) (h_ne : A ≠ B) 
(h_cube_eq : ∀ i j, (A ^ 3) i j = (B ^ 3) i j) (h_comm : ∀ i j, (A ^ 2 * B) i j = (B ^ 2 * A) i j) : 
¬IsUnit (A ^ 2 + B ^ 2) := sorry

theorem exists_close_diophantine_approx (h k : ℕ) (ε : ℝ) (hε : ε > 0) : 
  ∃ m n : ℕ, ε < |(h : ℝ) * Real.sqrt ↑m - (k : ℝ) * Real.sqrt ↑n| ∧ 
  |(h : ℝ) * Real.sqrt ↑m - (k : ℝ) * Real.sqrt ↑n| < 2 * ε := sorry

theorem u_in_Z (u : ℕ → ℤ) (h0 : u 0 = 1) (h1 : u 1 = 1) (h2 : u 2 = 1) (hdet : ∀ n : ℕ, Matrix.det (!![u n, u (n + 1); u (n + 2), u (n + 3)]) = Nat.factorial n) : ∀ n : ℕ, u n ∈ ℤ := sorry

theorem matrix_sum_trace_zero_implies_zero_matrix (n r : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℝ)) (hG_card : Nat.card G = r) (hG_inv : ∀ M ∈ G, IsUnit M) (hG_mul : ∀ M1 M2 ∈ G, M1 * M2 ∈ G) (h_trace_sum : ∑ i in Finset.range r, (trace (Nat.cast r ▸ (Nat.rec (fun _ => 0) (fun k rec => if k ∈ G then rec k + k else rec k) r))) = 0) : ∑ i in Finset.range r, (Nat.cast r ▸ (Nat.rec (fun _ => 0) (fun k rec => if k ∈ G then rec k + k else rec k) r)) = 0 := sorry

theorem proj_y_closed (S : Set (ℝ × ℝ)) (hS_closed : IsClosed S) (a b : ℝ) (hS_bounded : ∀ (p : ℝ × ℝ), p ∈ S → a < p.1 ∧ p.1 < b) : IsClosed {y : ℝ | ∃ x, (x, y) ∈ S} := sorry

theorem exists_palindrome_with_many_bases : ∃ n : ℕ, ∃ (B : Finset ℕ), B.card ≥ 2002 ∧ ∀ b ∈ B, b ≥ 2 ∧ ∃ (d0 d1 : ℕ), d0 ∈ Finset.Icc 1 (b - 1) ∧ d1 ∈ Finset.Icc 0 (b - 1) ∧ n = d0 * b^2 + d1 * b + d0 := sorry

theorem exists_jump_sequence_with_cost (c : ℝ) : (1/3 < c ∧ c ≤ 1) ↔ ∃ (n : ℕ) (xs : Fin (n + 1) → ℝ), (∀ (i : Fin n), xs (Fin.castSucc i) < xs (Fin.succ i)) ∧ xs 0 = 0 ∧ xs (Fin.last n) = 1 ∧ (∑ i : Fin n, (xs (Fin.succ i))^3 - xs (Fin.castSucc i) * (xs (Fin.succ i))^2) = c := sorry

theorem exists_shared_part_sizes (S : Finset ℕ) (hS : S = {1, 2, 3, 4, 5, 6, 7, 8, 9}) (π π' : Setoid (↑S)) : ∃ (x y : ↑S), x ≠ y ∧ Setoid.Class.card (Setoid.mkClasses π h) x = Setoid.Class.card (Setoid.mkClasses π h) y ∧ Setoid.Class.card (Setoid.mkClasses π' h') x = Setoid.Class.card (Setoid.mkClasses π' h') y := sorry

theorem sum_one_div_b_converges (a : ℕ → ℕ) (ha : ∀ n, a n < a (n + 1)) (b : ℕ → ℕ) (hb : ∀ n, b n = Finset.lcm (Finset.range (n + 1)) (a ∘ Nat.succ)) : Summable fun n => (1 : ℝ) / b n := sorry

theorem expected_connected_regions_size (m n : ℕ) :
  let G := Finset.product (Finset.range m) (Finset.range n);
  ∀ (c : ℕ × ℕ → ℕ), (∀ (i j : ℕ), (i, j) ∈ G → c (i, j) ∈ {0, 1}) →
  (∀ (i j : ℕ), (i, j) ∈ G → ProbabilityTheory.ℙ (c (i, j) = 0) = 1/2 ∧ ProbabilityTheory.ℙ (c (i, j) = 1) = 1/2) →
  ProbabilityTheory.ProbabilityMeasure.indepFun (Prod.fst ∘ c) (Prod.snd ∘ c) →
  let R := {S : Set (ℕ × ℕ) | ∃ (color : ℕ), (∀ p ∈ S, c p = color) ∧ IsConnected S};
  (∑ r in R, Finset.card r) > (m * n) / 8 := sorry

theorem diff_eq_solution (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (h : ∀ x, f x ^ 2 = ∫ t in 0..x, (f t ^ 2 + (deriv f t) ^ 2) + 1990) : ∀ x, f x = Real.sqrt 1990 * Real.exp x ∨ f x = -Real.sqrt 1990 * Real.exp x := sorry

theorem sum_of_squares_eq_sum_of_products (a b c d : ℤ) (S : Finset ℤ) (hS : S = {a, b, c, d}) (hmin : ∀ N : ℤ, ∃ x ∈ S, x ≥ N) : a^2 + b^2 + c^2 + d^2 = a*b*c + a*b*d + a*c*d + b*c*d := sorry

theorem exists_integer_combination_approximation (v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 : ℝ × ℝ × ℝ) (hv1 : ∀ i ∈ ({v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12} : Set (ℝ × ℝ × ℝ)), norm i = 1) (hico : IsIcosahedronSet {v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12}) (v : ℝ × ℝ × ℝ) (ε : ℝ) (hε : ε > 0) : ∃ (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : ℤ), norm (a1 • v1 + a2 • v2 + a3 • v3 + a4 • v4 + a5 • v5 + a6 • v6 + a7 • v7 + a8 • v8 + a9 • v9 + a10 • v10 + a11 • v11 + a12 • v12 - v) < ε := sorry

theorem limit_of_gcd_diverges (n : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A = !![3, 2; 4, 3]) (I : Matrix (Fin 2) (Fin 2) ℤ) (hI : I = !![1, 0; 0, 1]) (dₙ : ℕ) (hdₙ : dₙ = Nat.gcd ((A ^ n - I) 0 0) ((A ^ n - I) 0 1)) : Filter.Tendsto (fun n => ↑dₙ) Filter.atTop Filter.atTop := sorry

theorem polynomial_identity (p : ℝ → ℝ) (hp : Polynomial.degree (Polynomial.ofFinsupp (Polynomial.toFinsupp p)) = 4) (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, p x ∈ Set.Icc 0 1) : ∀ x, p x = 4 * x^4 - 4 * x^2 + 1 := sorry

theorem binomial_gcd_div_n_nat (m n : ℕ) (h : n ≥ m ∧ m ≥ 1) : ↑(Nat.gcd m n) / ↑n * ↑(Nat.choose n m) ∈ ℕ := sorry

theorem determinant_special_matrix (n : ℕ) : Matrix.det (fun (i j : Fin n) => (1 : ℚ) / min (↑i + 1) (↑j + 1)) = (-1 : ℚ)^(n - 1) / (Nat.factorial (n - 1) * Nat.factorial n) := sorry

theorem sum_powers_mod_condition (j : ℕ) :
  let A := {n : ℕ | 1 ≤ n ∧ n ≤ 2021 ∧ Nat.gcd n 2021 = 1};
  let S := fun j => ∑ n in A, n ^ j;
  let p := 43;
  let q := 47;
  p * q = 2021 →
  (S j ≡ 0 [MOD 2021] ↔ j % 42 ≠ 0 ∧ j % 46 ≠ 0) := sorry

theorem sequence_count_bound (n : ℤ) (hn : n ≥ 2) :
  let S := {s : Fin (Int.toNat (n - 1)) → ℤ | ∀ i, s i = 1 ∨ s i = -1};
  let P := Equiv.Perm (Fin (Int.toNat n));
  let f (s : Fin (Int.toNat (n - 1)) → ℤ) := Fintype.card {p : P | ∀ i, s i * (↑(p (Fin.succ i)) - ↑(p i)) > 0};
  let s_star1 (i : Fin (Int.toNat (n - 1))) := (-1 : ℤ) ^ (↑i + 1);
  let s_star2 (i : Fin (Int.toNat (n - 1))) := (-1 : ℤ) ^ (↑i);
  ∀ s ∈ S, f s ≤ f s_star1 ∧ f s ≤ f s_star2 ∧ (f s = f s_star1 ∨ f s = f s_star2 ↔ s = s_star1 ∨ s = s_star2) := sorry

theorem exists_potential_function (n : ℕ) (x : Fin n → ℝ) (f : Fin n → (Fin n → ℝ) → ℝ) 
  (hf : ∀ i j, ContDiff ℝ 2 (f i)) (c : Matrix (Fin n) (Fin n) ℝ) 
  (hc : ∀ i j, (fun x => fderiv ℝ (f i) x (Pi.single j 1)) - (fun x => fderiv ℝ (f j) x (Pi.single i 1)) = fun _ => c i j) :
  ∃ g : (Fin n → ℝ) → ℝ, ∀ i, (fun x => f i x + fderiv ℝ g x (Pi.single i 1)) ∈ LinearMap.module ℝ ℝ ℝ := sorry

theorem volume_calculation (x y z : ℝ) (r := Real.sqrt (x^2 + y^2)) (R : Set (ℝ × ℝ × ℝ) := {p : ℝ × ℝ × ℝ | (p.1^2 + p.2.1^2 + p.2.2^2 + 8)^2 ≤ 36 * (p.1^2 + p.2.1^2)}) : volume R = 6 * Real.pi^2 := sorry

theorem limit_G_zero : ∃ (G : ℝ≥0 → ℝ), (∀ (r : ℝ≥0), G r = Inf {|(r : ℝ) - Real.sqrt (↑(m^2) + 2 * ↑(n^2))| | (m : ℤ) (n : ℤ)}) ∧ Filter.Tendsto G Filter.atTop (nhds 0) := sorry

theorem count_special_pairs : ∃ N : ℕ, (2020 ∣ N) ∧ (Nat.log10 N + 1 ≤ 2020) ∧ 
  (∃ k m : ℕ, (Nat.digits 10 N).take k = List.replicate k 1 ∧ 
              (Nat.digits 10 N).drop k = List.replicate m 0 ∧ 
              k + m ≤ 2020) ∧ 
  Finset.card (Finset.filter (fun (k, m) => (Nat.div (10^k - 1) 9 * 10^m) % 2020 = 0 ∧ k + m ≤ 2020) 
    (Finset.product (Finset.range 2021) (Finset.range 2021))) = 508536 := sorry

theorem color_stabilizes (C₀ : ℝ⁺ → Fin 2) :
  ∃ (N : ℕ), ∀ (z : ℝ⁺), (Nat.rec (fun n Cₙ => fun z => if ∃ (x y : ℝ⁺), Cₙ x = Cₙ y ∧ dist x y = z then 0 else 1) C₀ N) z = 0 := sorry

theorem polynomial_roots_count (P : ℝ → ℝ) [Polynomial P] (Q : ℝ → ℝ) (hQ : ∀ x, Q x = (x^2 + 1) * P x * Polynomial.derivative P x + x * (P x^2 + (Polynomial.derivative P x)^2)) (n : ℕ) (roots : Finset ℝ) (hroots : ∀ r ∈ roots, P r = 0 ∧ r > 1) (hdistinct : Function.Injective (fun r : roots => (r : ℝ))) (hcard : Finset.card roots = n) : ∃ (s : Finset ℝ), (∀ q ∈ s, Q q = 0) ∧ Function.Injective (fun q : s => (q : ℝ)) ∧ Finset.card s ≥ 2 * n - 1 := sorry

theorem probability_bound (n : ℕ) (hn : n ≥ 1995) :
  let M := Matrix (Fin 3) (Fin n) ℕ
  let perm := {f : Fin 3 → Fin 3 | Function.Bijective f}
  let μ := ProbabilityTheory.measureOfProbabilitySpace (Fin n → perm)
  let a b c : ℕ := (Finset.sum Finset.univ fun j => M 0 j, Finset.sum Finset.univ fun j => M 1 j, Finset.sum Finset.univ fun j => M 2 j)
  let sorted := List.sort (· ≤ ·) [a, b, c]
  let a' := sorted.get 0
  let b' := sorted.get 1
  let c' := sorted.get 2
  μ {M | b' = a' + 1 ∧ c' = a' + 2} ≥ 4 * μ {M | a' = b' ∧ b' = c'} := sorry

theorem limit_of_product_sequence : Filter.Tendsto (fun n : ℕ ↦ ∏ k in Finset.range (n + 1 - 2), ((↑(k + 2) : ℚ)^3 - 1) / ((↑(k + 2) : ℚ)^3 + 1)) Filter.atTop (nhds (2/3 : ℚ)) := sorry

theorem exists_subset_with_lower_bound (f : ℝ → ℝ) (hf : MeasureTheory.IntegrableOn f (Set.Icc 0 1)) 
  (h_zero : ∀ (i : ℕ), i < n → ∫ x in 0..1, x^i * f x = 0) 
  (h_one : ∫ x in 0..1, x^n * f x = 1) : 
  ∃ (S : Set ℝ), MeasurableSet S ∧ ↑(MeasureTheory.volume S) > 0 ∧ ∀ x ∈ S, |f x| ≥ 2^n * (n + 1) := sorry

theorem sum_dist_sq_le_n_sq (n : ℕ) (S : Set (ℝ × ℝ × ℝ)) (hS : Nat.card S = n) 
  (hS_sphere : ∀ p ∈ S, ∃ x y z, p = (x, y, z) ∧ x^2 + y^2 + z^2 = 1) : 
  ∑ p in S.toFinset, ∑ q in S.toFinset, if p ≠ q then dist p q ^ 2 else 0 ≤ n^2 := sorry

theorem limit_prob_sum_uniform_perfect_square (n : ℕ) (c d : Fin n → ℕ) [UniformDistrib c] [UniformDistrib d] : 
    Tendsto (fun n ↦ (probability (fun x ↦ ∃ k, c x + d x = k ^ 2) * Real.sqrt ↑n)) atTop (nhds ((4/3) * (Real.sqrt 2 - 1))) := sorry

theorem exists_subset_sum_with_non_divisible_elements (n : ℕ) :
  ∃ T ⊆ {p : ℕ × ℕ | p.1 ≥ 0 ∧ p.2 ≥ 0},
    (∑ p in T, 2^p.1 * 3^p.2 = n) ∧
    (∀ (p₁ p₂ : ℕ × ℕ), p₁ ∈ T → p₂ ∈ T → p₁ ≠ p₂ → ¬(2^p₁.1 * 3^p₁.2 ∣ 2^p₂.1 * 3^p₂.2)) := sorry

theorem nat_frac_inequality (a b c d : ℕ) (h₁ : a + c ≤ 1982) (h₂ : ↑a / ↑b + ↑c / ↑d < (1 : ℝ)) : 1 - ↑a / ↑b - ↑c / ↑d > 1 / (1983 ^ 3) := sorry

theorem area_sum_nonnegative (m : ℕ) (hm : m ≥ 3) (N : ℕ := Nat.choose m 3) (a : {p : ℕ × ℕ × ℕ // 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < p.3 ∧ p.3 ≤ m} → ℝ) (ha : ∀ (A : Fin m → ℝ × ℝ), ∑ (p : {p : ℕ × ℕ × ℕ // 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < p.3 ∧ p.3 ≤ m}), a p • EuclideanGeometry.area (A ⟨p.1.1, sorry⟩) (A ⟨p.1.2, sorry⟩) (A ⟨p.1.3, sorry⟩) ≥ 0) : ∀ (B : Fin m → ℝ × ℝ × ℝ), ∑ (p : {p : ℕ × ℕ × ℕ // 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < p.3 ∧ p.3 ≤ m}), a p • EuclideanGeometry.area (B ⟨p.1.1, sorry⟩) (B ⟨p.1.2, sorry⟩) (B ⟨p.1.3, sorry⟩) ≥ 0 := sorry

theorem integral_bound (f : ℝ → ℝ) (hdiff : DifferentiableOn ℝ f (Set.Icc 0 1)) (hcont : ContinuousOn (deriv f) (Set.Icc 0 1)) (hint : ∫ x in 0..1, f x = 0) (α : ℝ) (hα : α ∈ Set.Ioo 0 1) : |∫ x in 0..α, f x| ≤ (1/8) * Real.sSup (Set.image (fun x => |deriv f x|) (Set.Icc 0 1)) := sorry

theorem count_functions_with_iterate_condition (n : ℕ) (X : Finset ℕ := Finset.range n) (k : ℕ) (hk : k ∈ X) (f : ℕ → ℕ) :
  (∀ x ∈ X, ∃ j : ℕ, (Nat.iterate f j x) ≤ k) → Fintype.card {f : ℕ → ℕ | ∀ x ∈ X, ∃ j : ℕ, (Nat.iterate f j x) ≤ k} = k * n^(n - 1) := sorry

theorem sum_diverges (a : ℕ → ℝ≥0) (h : ∀ n : ℕ, 0 < a n ∧ a n ≤ a (2 * n) + a (2 * n + 1)) : ¬Summable a := sorry

theorem group_identity {G : Type*} [Group G] (A B : G) (h1 : A * B * A = B * A^2 * B) (h2 : A^3 = 1) (n : ℕ) (h3 : B^(2 * n - 1) = 1) : B = 1 := sorry

theorem ratio_of_areas_rational (A B C D : ℝ × ℝ) (h_distinct : A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D) (h_colinear : ∀ S : Finset (ℝ × ℝ), S ⊆ {A, B, C, D} → S.card = 3 → ¬Collinear S) (d : (ℝ × ℝ) × (ℝ × ℝ) → ℝ) (h_d : ∀ p q, d p q = Real.dist p.1 p.2 q.1 q.2) (h_AB : (d (A, B))^2 ∈ Rat) (h_AC : (d (A, C))^2 ∈ Rat) (h_AD : (d (A, D))^2 ∈ Rat) (h_BC : (d (B, C))^2 ∈ Rat) (h_BD : (d (B, D))^2 ∈ Rat) (h_CD : (d (C, D))^2 ∈ Rat) : (EuclideanGeometry.area (⟨A, B, C⟩ : EuclideanGeometry.Triangle (ℝ × ℝ))) / EuclideanGeometry.area (⟨A, B, D⟩ : EuclideanGeometry.Triangle (ℝ × ℝ)) ∈ Rat := sorry

theorem exists_N_for_positive_coefficients (ε : ℝ) (hε : 0 < ε ∧ ε < 1) (x y : ℝ) (n : ℤ) : ∃ N : ℕ, ∀ (n : ℕ), ↑n ≥ ↑N → ∀ (k : ℕ), k ≤ 2 * n + 2 → 0 < Polynomial.coeff (Polynomial.mul (Polynomial.expand ℝ (↑n + 1) (Polynomial.X + Polynomial.Y)) (Polynomial.C (x^2 - (2 + ε) * x * y + y^2))) k := sorry

theorem exists_unique_n_in_S_with_infinite_congruent_iterates : ∃! n ∈ {n : ℕ | 0 ≤ n ∧ n ≤ 99}, (∃ᶠ i in Filter.atTop, (fun i => a i) i ≡ n [MOD 100]) ∧ n = 87 := sorry

theorem f_n_nonzero (n : ℕ) (f_n : ℂ → ℂ) (h_def : ∀ z : ℂ, f_n z = ∑ k in Finset.range n, (↑n - ↑k) * z ^ k) (z : ℂ) (h_z : Complex.abs z ≤ 1) : f_n z ≠ 0 := sorry

theorem limit_of_E_over_n_squared (E : ℕ → ℤ) (hE : ∀ n, E n = Int.greatest (fun k => (5^k) ∣ ∏ i in Finset.range (n + 1), i^i)) : Filter.Tendsto (fun n => (E n : ℝ) / (n : ℝ)^2) Filter.atTop (𝓝 (1/8)) := sorry

theorem goal (n : ℕ) : T n = A n + B n := sorry

theorem primes_with_count_ge_seven : {p ∈ Nat.Prime | let S := {(p, q, r) ∈ Nat.Prime × Nat.Prime × Nat.Prime | ∃ (x : ℚ), p * x^2 + q * x + r = 0}; let count := fun p ↦ Finset.card {(q, r) ∈ Nat.Prime × Nat.Prime | (p, q, r) ∈ S}; count p ≥ 7} = {2, 5} := sorry

theorem equilateral_triangle_condition (r : ℝ) (hr : r > 0) (A B C D E F : ℝ × ℝ) (hdistinct : Pairwise (Ne on ![A, B, C, D, E, F])) (hon_circle : ∀ P ∈ ({A, B, C, D, E, F} : Set (ℝ × ℝ)), dist P (0, 0) = r) (hAB : dist A B = r) (hCD : dist C D = r) (hEF : dist E F = r) (M : ℝ × ℝ) (hM : M = midpoint ℝ B C) (N : ℝ × ℝ) (hN : N = midpoint ℝ D E) (O : ℝ × ℝ) (hO : O = midpoint ℝ F A) : ∃ s : ℝ, dist M N = s ∧ dist N O = s ∧ dist O M = s := sorry

theorem angle_condition (A B C : ℝ × ℝ) (angle_CAB angle_BCA angle_ABC : ℝ) (h_triangle : List.Nodup [A, B, C]) (h_angles : angle_CAB < angle_BCA ∧ angle_BCA < Real.pi / 2 ∧ Real.pi / 2 < angle_ABC) (P : ℝ × ℝ) (hP : P ∈ AffineSegment ℝ B C ∧ P ≠ B ∧ P ≠ C ∧ ∃ (l : Line ℝ (ℝ × ℝ)), l = Line.externalAngleBisector A B C ∧ P ∈ l ∧ P ∈ Line ℝ B C) (Q : ℝ × ℝ) (hQ : Q ∈ AffineSegment ℝ C A ∧ Q ≠ C ∧ Q ≠ A ∧ ∃ (l : Line ℝ (ℝ × ℝ)), l = Line.externalAngleBisector B C A ∧ Q ∈ l ∧ Q ∈ Line ℝ C A) (h_dist : dist A P = dist B Q ∧ dist B Q = dist A B) : angle_CAB = Real.pi / 15 := sorry

theorem sequence_periodic (a : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 1) (hx1 : x 1 = a) (hx2 : x 2 = a) 
  (hrec : ∀ n ≥ 2, x (n + 1) = 2 * x n * x (n - 1) - x (n - 2)) (hex : ∃ n, x n = 0) : 
  ∃ p > 0, ∀ n, x (n + p) = x n := sorry

theorem prime_sum_diff_not_cong {p : ℕ} (hp : p ∈ {3, 5, 7, 11}) (hprime : Nat.Prime p) (F : ℤ → ℤ) (hF : ∀ n : ℤ, F n = ∑ k in Finset.Icc 1 (p - 1), k * n^(k - 1)) (a b : ℤ) (ha : a ∈ Set.Icc (0 : ℤ) (p - 1)) (hb : b ∈ Set.Icc (0 : ℤ) (p - 1)) (hne : a ≠ b) : ¬(F a - F b ≡ 0 [ZMOD p]) := sorry

theorem power_series_expansion (m : ℕ) (h₁ : m > 1) (h₂ : Odd m) (n := 2 * m) (θ : ℂ) (hθ : θ = Complex.exp (2 * π * Complex.I / ↑n)) : (1 - θ)⁻¹ = ∑ k in Finset.range m, if Even k then 0 else θ ^ k := sorry

theorem integral_inequality (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) : 
(∫ x in 0..1, ∫ y in 0..1, |f x + f y|) ≥ (∫ x in 0..1, |f x|) := sorry

theorem integral_ln_over_quadratic : 
  let f : ℝ → ℝ := fun x => Real.log (x + 1) / (x^2 + 1); 
  let I := ∫ x in (0:ℝ)..1, f x; 
  I = (Real.pi / 8) * Real.log 2 := sorry

theorem exists_poly_floor_eq_f : ∃ (p : ℝ → ℝ), ∀ (n : ℕ), f n = Int.floor (p ↑n) := sorry

theorem fixed_point_equation (x : ℝ) (hx : x = 2207 - (1 / x)) : x ^ (1 / 8) = (3 + 1 * Real.sqrt 5) / 2 := sorry

theorem S_eq_T : {N : ℕ | ∃ (k : ℕ) (d : ℕ → ℕ), (∀ i, d i ∈ Finset.Icc 0 10) ∧ d k ≠ 0 ∧ N = ∑ i in Finset.range (k + 1), d i * 10 ^ i ∧ ∀ (k' : ℕ) (d' : ℕ → ℕ), (∀ i, d' i ∈ Finset.Icc 0 10) → d' k' ≠ 0 → N = ∑ i in Finset.range (k' + 1), d' i * 10 ^ i → k = k' ∧ ∀ i, d i = d' i} = {N : ℕ | ∃ (k : ℕ) (d : ℕ → ℕ), (∀ i, d i ∈ Finset.Icc 0 9) ∧ d k ≠ 0 ∧ N = ∑ i in Finset.range (k + 1), d i * 10 ^ i ∧ ∀ i, d i ≠ 0} := sorry

theorem largest_partition_equal_sums (n : ℕ) (hn : n > 0) : 
  ∃ (S : Finset ℕ) (total_sum k_max : ℕ), S = Finset.range n ∧ 
  total_sum = n * (n + 1) / 2 ∧ k_max = Nat.ceil (↑n / (2 : ℝ)) ∧ 
  (∀ k, k ≤ k_max → ∃ (P : Finset (Finset ℕ)), P.pairwiseDisjoint id ∧ 
  P.sup id = S ∧ ∀ t ∈ P, Finset.sum t id = total_sum / k) ∧ 
  (∀ k, k > k_max → ¬∃ (P : Finset (Finset ℕ)), P.pairwiseDisjoint id ∧ 
  P.sup id = S ∧ ∀ t ∈ P, Finset.sum t id = total_sum / k) := sorry

theorem determinant_sequence_unbounded : ¬BddAbove {S n | (n : ℕ) (hn : n ≥ 2)} := sorry

theorem exists_distinct_points_with_midpoint (S : Set (ℤ × ℤ × ℤ)) (hS : Nat.card S = 9) : ∃ p1 ∈ S, ∃ p2 ∈ S, p1 ≠ p2 ∧ ∃ q : ℤ × ℤ × ℤ, ∃ t : ℚ, 0 < t ∧ t < 1 ∧ q = (1 - t) • p1 + t • p2 := sorry

theorem exists_point_with_gradient_bound (f : ℝ × ℝ → ℝ) (h_diff : ∀ (p : ℝ × ℝ), p.1^2 + p.2^2 ≤ 1 → DifferentiableAt ℝ f p) (h_bound : ∀ (p : ℝ × ℝ), p.1^2 + p.2^2 ≤ 1 → |f p| ≤ 1) : ∃ (p : ℝ × ℝ), p.1^2 + p.2^2 < 1 ∧ (deriv (fun x => f (x, p.2)) p.1)^2 + (deriv (fun y => f (p.1, y)) p.2)^2 ≤ 16 := sorry

theorem tangent_condition (α : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = α * x^2 + α * x + (1 / 24)) (g : ℝ → ℝ) (hg : ∀ y, g y = α * y^2 + α * y + (1 / 24)) : (∃ x y, f x = y ∧ g y = x ∧ (Function.HasDerivAt f (2 * α * x + α) x ∧ Function.HasDerivAt g (2 * α * y + α) y ∧ (2 * α * x + α) * (2 * α * y + α) = 1)) ↔ α ∈ ({2/3, 3/2, (13 + Real.sqrt 601)/12, (13 - Real.sqrt 601)/12} : Set ℝ) := sorry

theorem sum_bound (m n k : ℕ) (a : ℕ × ℕ → ℤ) (ha : ∀ m n, a (m, n) = Polynomial.coeff ℤ ((1 + Polynomial.X + Polynomial.X ^ 2) ^ m) n) (hk : k ≥ 0) : 
let S := {i : ℕ | 0 ≤ i ∧ i ≤ Nat.floor (2 * k / 3)};
0 ≤ ∑ i in S, (-1 : ℤ) ^ i * a (k - i, i) ∧ ∑ i in S, (-1 : ℤ) ^ i * a (k - i, i) ≤ 1 := sorry

theorem formalized (k : ℕ) (hk : ∀ (l : ℕ), 0 < l → (∃ (m1 m2 m3 m4 m5 : ℤ), Distinct (m1 :: m2 :: m3 :: m4 :: m5 :: []) ∧ (∀ (x : ℤ), (fun x => (x - m1) * (x - m2) * (x - m3) * (x - m4) * (x - m5)) x = (fun x => (x - m1) * (x - m2) * (x - m3) * (x - m4) * (x - m5)) x) ∧ (Finset.card (Finset.filter (fun c => c ≠ 0) (Finset.range (k + 1)).toFinset) = k)) → k ≤ l) : (Finset.card (Finset.filter (fun c => c ≠ 0) (Finset.range (6)).toFinset) = 3) ∧ k = 3 := sorry

theorem optimization_on_S (a b c : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
  let S := {p : ℝ × ℝ × ℝ | p.1^b + p.2.1^b + p.2.2^b = 1 ∧ p.1 ≥ 0 ∧ p.2.1 ≥ 0 ∧ p.2.2 ≥ 0};
  let f : ℝ × ℝ × ℝ → ℝ := fun (x, y, z) => x^a + y^b + z^c;
  let x0 := (a / b)^(1 / (b - a));
  let z0 := (b / c)^(1 / (c - b));
  IsMaxOn f S (x0, (1 - x0^b)^(1/b), 0) ∧ IsMinOn f S (0, (1 - z0^b)^(1/b), z0) := sorry

theorem dancing_relation_condition (B G : Set ℕ) (D : Set (ℕ × ℕ)) (hD : D ⊆ B ×ˢ G) 
  (hB : ∀ b ∈ B, ∃ g ∈ G, (b, g) ∉ D) (hG : ∀ g ∈ G, ∃ b ∈ B, (b, g) ∈ D) : 
  ∃ g h ∈ G, ∃ b c ∈ B, (b, g) ∈ D ∧ (c, h) ∈ D ∧ (b, h) ∉ D ∧ (c, g) ∉ D := sorry

theorem limit_sequence_a (a : ℕ → ℝ) (h : ∀ n, a n = (1 / (n : ℝ)^4) * ∏ i in Finset.range (2 * n), (n^2 + i^2 : ℝ)^(1 / (n : ℝ))) : Filter.Tendsto a Filter.atTop (nhds (Real.exp (2 * Real.log 5 - 4 + 2 * Real.arctan 2))) := sorry

theorem sum_converges_and_equals (a : ℕ → ℝ≥0) (b : ℕ → ℝ≥0) (ha1 : a 1 = 1) (hb1 : b 1 = 1) 
  (hrec : ∀ n ≥ 2, b n = b (n - 1) * a n - 2) (hbounded : ∃ M : ℝ, ∀ j : ℕ, ↑(b j) ≤ M) :
  Summable (fun n ↦ 1 / ∏ k in Finset.range (n + 1), ↑(a k)) ∧ 
  ∑' n, 1 / ∏ k in Finset.range (n + 1), ↑(a k) = 3/2 := sorry

theorem line_intersection_condition (L1 L2 : Set (ℝ × ℝ)) (hL1 : ∃ a b c, a ≠ 0 ∨ b ≠ 0 ∧ L1 = {p | a * p.1 + b * p.2 + c = 0}) (hL2 : ∃ a b c, a ≠ 0 ∨ b ≠ 0 ∧ L2 = {p | a * p.1 + b * p.2 + c = 0}) (hL1_ne_L2 : L1 ≠ L2) (P : ℝ × ℝ) (hP1 : P ∉ L1) (hP2 : P ∉ L2) : 
(L1 ∩ L2 ≠ ∅) ↔ (∀ λ ∈ ℝ, λ ≠ 0 → ∃ A1 ∈ L1, ∃ A2 ∈ L2, (A2.1 - P.1, A2.2 - P.2) = λ • (A1.1 - P.1, A1.2 - P.2)) := sorry

theorem exists_derivative_negative (f : ℝ → ℝ) (hf : ContDiff ℝ ⊤ f) (h0 : f 0 = 0) (h1 : f 1 = 1) (hpos : ∀ x, f x ≥ 0) : ∃ (n : ℕ) (x : ℝ), n > 0 ∧ (iteratedDeriv n f x < 0) := sorry

theorem smallest_constant_for_cubic_polynomial_integral (P : ℝ → ℝ) (hP : Polynomial P) (degP : Polynomial.natDegree P = 3) (∃ r ∈ Set.Icc 0 1, P r = 0) : 
    ∃! C, (∀ P, (Polynomial P ∧ Polynomial.natDegree P = 3 ∧ ∃ r ∈ Set.Icc 0 1, P r = 0) → 
    let M := sSup (Set.image (fun x => |P x|) (Set.Icc 0 1)) in 
    ∫ x in 0..1, |P x| ≤ C * M) ∧ 
    C = 5/6 := sorry

theorem injective_f {f : ℝ × ℝ → ℝ × ℝ} (f1 : ℝ × ℝ → ℝ) (f2 : ℝ × ℝ → ℝ) 
(hf : ∀ p : ℝ × ℝ, f p = (f1 p, f2 p))
(hdiff : ∀ (i j : Fin 2), ContDiff ℝ 1 (fun p : ℝ × ℝ → ![f1 p, f2 p] i j))
(hpos : ∀ (i j : Fin 2) (p : ℝ × ℝ), HasDerivAt (fun x : ℝ → ![f1 (Function.update p i x), f2 (Function.update p i x)] j) (∂f_i/∂x_j p) (p i))
(hcond : ∀ p : ℝ × ℝ, (∂f1/∂x1 p) * (∂f2/∂x2 p) - (1/4) * (∂f1/∂x2 p + ∂f2/∂x1 p)^2 > 0) :
∀ a b : ℝ × ℝ, f a = f b → a = b := sorry

theorem derivative_polynomial_at_one (k : ℕ) (f : ℝ → ℝ) (hf : ∀ x, x ≠ 1 ∨ k = 0 → f x = 1 / (x^k - 1)) (P : ℕ → ℝ → ℝ) (hP : ∀ n, ∀ x, x ≠ 1 ∨ k = 0 → deriv^[n] f x = P n x / (x^k - 1)^(n + 1)) : ∀ n, P n 1 = (-k)^n * Nat.factorial n := sorry

theorem exists_graph_without_triangle {V E : ℕ} (h : 4 * E ≤ V ^ 2) : ∃ (G : SimpleGraph (Fin V)), card (SimpleGraph.edgeFinset G) = E ∧ ∀ (u v w : Fin V), u ≠ v → v ≠ w → u ≠ w → ¬(SimpleGraph.Adj G u v ∧ SimpleGraph.Adj G v w ∧ SimpleGraph.Adj G u w) := sorry

theorem diff_eq_solution (f g h : ℝ → ℝ) (hf : DifferentiableOn ℝ f (Set.Ioo (-1) 1)) (hg : DifferentiableOn ℝ g (Set.Ioo (-1) 1)) (hh : DifferentiableOn ℝ h (Set.Ioo (-1) 1)) (f' : ∀ x, f' x = 2 * f x ^ 2 * g x * h x + (1 / (g x * h x))) (g' : ∀ x, g' x = f x * g x ^ 2 * h x + (4 / (f x * h x))) (h' : ∀ x, h' x = 3 * f x * g x * h x ^ 2 + (1 / (f x * g x))) (f0 : f 0 = 1) (g0 : g 0 = 1) (h0 : h 0 = 1) : ∀ x, f x = 2 ^ (-1/12) * ((Real.sin (6 * x + Real.pi / 4) / (Real.cos (6 * x + Real.pi / 4) ^ 2)) ^ (1/6)) := sorry

theorem growth_condition_implies_r_eq_one_fourth (r : ℝ) (g : ℕ → ℕ) (h : ∀ n : ℕ, g (n + 1) - g n ≥ (g (g n)) ^ r) : r = 1 / 4 := sorry

theorem exists_fraction_condition : 
  let A := {1, 2, 3}; 
  let B := {1, 2, ..., 2024}; 
  let C := {1, 2, ..., 6072}; 
  let S := {T : A × B → C | Function.Bijective T ∧ 
    (∀ j ∈ B, T (1, j) < T (2, j) < T (3, j)) ∧ 
    (∀ i ∈ A, ∀ j ∈ {1, 2, ..., 2023}, T (i, j) < T (i, j + 1))} in 
  ∃ a c ∈ A, ∃ b d ∈ B, 
    (1/3 : ℝ) ≤ (Nat.card {T ∈ S | T (a, b) < T (c, d)}) / Nat.card S ∧ 
    (Nat.card {T ∈ S | T (a, b) < T (c, d)}) / Nat.card S ≤ (2/3 : ℝ) := sorry

theorem polynomial_existence (n : ℕ) : ∃ (H : Polynomial (ℝ × ℝ → ℝ)), (∀ (x y : ℝ), H.eval (P x y, Q x y) = F n x y) ∨ (∀ (x y : ℝ), H.eval (P x y, Q x y) = G n x y) := sorry
where
  P (x y : ℝ) := x^2 * y + x * y^2
  Q (x y : ℝ) := x^2 + x * y + y^2
  F (n : ℕ) (x y : ℝ) := (x + y)^n - x^n - y^n
  G (n : ℕ) (x y : ℝ) := (x + y)^n + x^n + y^n

theorem dimension_of_V : ∃ (V : Set (Polynomial ℝ (Fin 2 → ℝ))), (∀ p ∈ V, Polynomial.totalDegree p ≤ 2009) ∧ (∀ p ∈ V, ∀ r ∈ ℝ⁺, (∫ θ in (0)..(2 * π), (Polynomial.eval (fun _ => r * Real.cos θ) p + Polynomial.eval (fun _ => r * Real.sin θ) p) / (2 * π)) = 0) ∧ Submodule ℝ (Subtype.val '' V) ∧ FiniteDimensional.finrank ℝ (Subtype.val '' V) = 2020050 := sorry

theorem sum_powers_binomial (k : ℕ) : ∑ j in Finset.range (k + 1), 2^(k - j) * Nat.choose (k + j) j = 4^k := sorry

theorem double_sum_identity (m n : ℕ) : 
    ∑' (m : ℕ), ∑' (n : ℕ), (m^2 * n) / (3^m * (n * 3^m + m * 3^n)) = (9 : ℝ) / 32 := sorry

theorem congruence_property (b : ℕ → ℤ) (h0 : b 0 = 0) (hrec : ∀ n, b (n + 1) = 2 * (b n)^2 + b n + 1) (k : ℕ) (hk : k ≥ 1) : (b (2^(k + 1)) - 2 * b (2^k)) ≡ 0 [ZMOD 2^(2 * k + 2)] ∧ ¬(b (2^(k + 1)) - 2 * b (2^k)) ≡ 0 [ZMOD 2^(2 * k + 3)] := sorry

theorem exists_c_satisfying_condition (I : Set ℝ) [Interval I] (f : I → ℝ) (hf : ContinuousOn f I) (y1 y2 : I → ℝ) 
(hy1'' : ∀ x ∈ I, HasDerivAt (fun x => HasDerivAt y1 (y1' x) x) (f x * y1 x) x) 
(hy2'' : ∀ x ∈ I, HasDerivAt (fun x => HasDerivAt y2 (y2' x) x) (f x * y2 x) x) 
(lindep : LinearIndependent ℝ ![y1, y2]) 
(hy1pos : ∀ x ∈ I, y1 x > 0) 
(hy2pos : ∀ x ∈ I, y2 x > 0) 
(c : ℝ) (hc : c > 0) 
(z : I → ℝ) (hz : ∀ x ∈ I, z x = c * Real.sqrt (y1 x * y2 x)) : 
∃ c > 0, ∀ x ∈ I, HasDerivAt (fun x => HasDerivAt z (z' x) x) (f x * z x - 1 / (z x)^3) x := sorry

theorem size_of_S : Finset.card (Finset.filter (fun (n : ℕ) => n ∣ 10^40 ∨ n ∣ 20^30) (Finset.Icc 1 (max (10^40) (20^30)))) = 2301 := sorry

theorem roots_in_unit_disk_implies_parameters_in_triangle (b c : ℝ) (f : ℂ → ℂ) (hf : ∀ z, f z = z^2 + b * z + c) (z1 z2 : ℂ) (h1 : f z1 = 0) (h2 : f z2 = 0) (h1_norm : Complex.abs z1 < 1) (h2_norm : Complex.abs z2 < 1) : (b, c) ∈ Set.Ioo (0, -1) (2, 1) ∪ Set.Ioo (0, -1) (-2, 1) := sorry

theorem exists_infinitely_many_pairs_triangular_numbers : ∃ (f : ℕ → ℤ × ℤ), Infinite (Set.range f) ∧ ∀ (n : ℕ), let T := fun (n : ℕ) => Nat.div (n * (n + 1)) 2; ∀ (t : ℕ), (∃ (k : ℕ), T k = t) ↔ (∃ (m : ℕ), T m = (f n).1 * ↑t + (f n).2) := sorry

theorem exists_large_triangle_containing_points (S : Finset (ℝ × ℝ)) (hS : ∀ (A B C : ℝ × ℝ), A ∈ S → B ∈ S → C ∈ S → |(Vec.det (Vec.cons (B.1 - A.1, B.2 - A.2) (Vec.cons (C.1 - A.1, C.2 - A.2) Vec.nil))) / 2| ≤ 1) : ∃ (T : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ), |(Vec.det (Vec.cons (T.2.1 - T.1.1, T.2.2 - T.1.2) (Vec.cons (T.3.1 - T.1.1, T.3.2 - T.1.2) Vec.nil))) / 2| = 4 ∧ ∀ (p : ℝ × ℝ), p ∈ S → pointInTriangle p (T.1, T.2, T.3) := sorry

theorem limit_sequence_ratio (k : ℕ) (hk : k > 1) (a₀ : ℝ) (ha₀ : a₀ > 0) (a : ℕ → ℝ) (ha : ∀ n : ℕ, a (n + 1) = a n + (a n) ^ (-(1 / ↑k))) : Filter.Tendsto (fun n => (a n) ^ (↑k + 1) / (↑n) ^ k) Filter.atTop (nhds (((↑k + 1) / ↑k) ^ k)) := sorry

theorem probability_min_eq (Ω : Type*) [MeasureSpace Ω] (X Y : Ω → ℤ) [IsProbabilityMeasure (ℙ : Measure Ω)] (hX : Finite (Set.range X)) (hY : Finite (Set.range Y)) (k : ℤ) : ℙ {ω | min (X ω) (Y ω) = k} = ℙ {ω | X ω = k} + ℙ {ω | Y ω = k} - ℙ {ω | max (X ω) (Y ω) = k} := sorry

theorem sum_divisors_divisible_by_24 (n : ℕ) (h : 24 ∣ (n + 1)) : 24 ∣ (∑ d in Nat.divisors n, d) := sorry

theorem exists_large_almost_disjoint_family (S : Set ℕ) (hS : Set.Countable S ∧ Set.Infinite S) (C : Set (Set S)) (hC : ∀ A ∈ C, Nat.card (Subtype.val '' A) ≥ 1) : ∃ C : Set (Set S), Nat.card C > Cardinal.aleph0 ∧ ∀ A ∈ C, ∀ B ∈ C, A ≠ B → Nat.card (Subtype.val '' (A ∩ B)) < Cardinal.aleph0 := sorry

theorem matrix_commutative_pair_exists (S : Set (Matrix (Fin 2) (Fin 2) ℤ)) (hS : ∀ M ∈ S, ∃ a b c d : ℤ, M = !![a, b; c, d] ∧ (∃ w x y z : ℤ, a = w^2 ∧ b = x^2 ∧ c = y^2 ∧ d = z^2)) (hB : ∀ M ∈ S, ∃ a b c d : ℤ, M = !![a, b; c, d] ∧ a ≤ 200 ∧ b ≤ 200 ∧ c ≤ 200 ∧ d ≤ 200) (hCard : Nat.card S > 50387) : ∃ M₁ M₂ ∈ S, M₁ ≠ M₂ ∧ M₁ * M₂ = M₂ * M₁ := sorry

theorem exists_point_with_zero_sum {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hbounded : ∀ x, |f x| ≤ 1) (hinit : f 0 ^ 2 + (deriv f 0) ^ 2 = 4) : ∃ y, f y + deriv (deriv f) y = 0 := sorry

theorem size_nonzero_f_mod_p (p : ℕ) (hp : Nat.Prime p) (hpgt2 : p > 2) :
  let S := Finset.Icc 0 (p - 1);
  let f := fun (n : ℕ) => ∑ k in Finset.Icc 0 (p - 1), (Nat.factorial k * n ^ k);
  Finset.card {n ∈ S | ¬(f n ≡ 0 [ZMod p])} ≥ (p + 1) / 2 := sorry

theorem inf_area_convex_set_intersecting_hyperbolas (S : Set (ℝ × ℝ)) (hS : Convex ℝ S) 
  (H1 : Set (ℝ × ℝ) := {p | p.1 * p.2 = 1}) (H2 : Set (ℝ × ℝ) := {p | p.1 * p.2 = -1})
  (h1 : S ∩ H1 ≠ ∅) (h2 : S ∩ H2 ≠ ∅) : 
  sInf (area '' {T | Convex ℝ T ∧ T ⊆ S}) = 4 := sorry

theorem integral_goal (t : ℝ) (ht : t > 0) : 
  (∫₀^∞ (fun t => t^(-1/2) * Real.exp (-1985 * (t + t⁻¹))) t) = Real.sqrt (π / 1985) * Real.exp (-3970) := sorry

theorem infinitely_many_consecutive_sums_of_two_squares : ∃ (f : ℕ → ℤ), Function.Injective f ∧ ∀ (k : ℕ), (∃ (a b : ℤ), f k = a^2 + b^2) ∧ (∃ (c d : ℤ), f k + 1 = c^2 + d^2) ∧ (∃ (e g : ℤ), f k + 2 = e^2 + g^2) := sorry

