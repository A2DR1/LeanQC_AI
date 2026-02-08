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

theorem quadrilateral_cyclic (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (S : ℝ) (hS_def : S = Real.sqrt (a * b * c * d)) (h_tangent : ∃ (circle : Set ℝ × ℝ), ∀ (side : ℝ), side ∈ ({a, b, c, d} : Set ℝ) → ∃ (tangent_point : ℝ), tangent_point ∈ circle.1 ∧ tangent_point = side) (h_area : let quadrilateral_area := S in quadrilateral_area = S) : ∃ (A B C D : ℝ × ℝ), let side_lengths : ℝ × ℝ × ℝ × ℝ := (a, b, c, d) in ∀ (P : ℝ × ℝ), P ∈ ({A, B, C, D} : Set (ℝ × ℝ)) → ∃ (Q : ℝ × ℝ), Q ∈ ({A, B, C, D} : Set (ℝ × ℝ)) ∧ dist P Q ∈ ({a, b, c, d} : Set ℝ) ∧ ∃ (center : ℝ × ℝ) (radius : ℝ), ∀ (vertex : ℝ × ℝ), vertex ∈ ({A, B, C, D} : Set (ℝ × ℝ)) → dist vertex center = radius := sorry

theorem digit_sum_roots (n : ℕ) (hn : n = 1010) (N : ℕ) (hN : N = 3^n - 1) (f : ℕ → ℕ) (hf : ∀ k, f k = ((Nat.digits 3 k).filter (· = 1)).length) (S : ℂ → ℂ) (hS : ∀ z, S z = ∑ k in Finset.range (N + 1), ((-2 : ℂ) ^ (f k)) * (z + (k : ℂ)) ^ 2023) :
    {z : ℂ | S z = 0} = {(-(N : ℂ)) / 2, (-(N : ℂ)) / 2 + (Real.sqrt ((9 : ℂ)^n - 1)) / 4 * Complex.I, (-(N : ℂ)) / 2 - (Real.sqrt ((9 : ℂ)^n - 1)) / 4 * Complex.I} := sorry

theorem noncollinear_triple_punch_union_covers_plane (A B C : ℝ × ℝ) (h_noncollinear : ¬Collinear ℝ ({A, B, C} : Set (ℝ × ℝ))) : ⋃ (X ∈ ({A, B, C} : Finset (ℝ × ℝ))), {P : ℝ × ℝ | Irrational (dist P X)} = Set.univ := sorry

theorem subset_product_covers_group (G : Type*) [Group G] [Fintype G] (A : Set G) (hA : Fintype.card A > (1/2 : ℚ) * Fintype.card G) : ∀ g : G, ∃ a b : G, a ∈ A ∧ b ∈ A ∧ g = a * b := sorry

theorem size_of_arithmetic_progression_set_zero : Finset.card (Finset.filter (λ (p : ℕ × ℕ) => let (n, r) := p in r + 3 ≤ n ∧ ∃ (d : ℚ), (C n (r + 1) - C n r = d) ∧ (C n (r + 2) - C n (r + 1) = d) ∧ (C n (r + 3) - C n (r + 2) = d)) (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (Finset.Ico 0 (Finset.sup (F

theorem exists_sum_of_divisors_multiple_of_24 (n : ℕ) (hn_pos : n > 0) (h_exists_k : ∃ k : ℤ, (n : ℤ) + 1 = 24 * k) : ∃ m : ℤ, (∑ d in (Nat.divisors n), d) = 24 * m := sorry

theorem rational_sequence_has_integer_factor (a : ℕ → ℚ) (h1 : a 1 = 1) (h2 : a 2 = 2) (h3 : a 3 = 24) (hrec : ∀ n ≥ 4, a n = ((6 * (a (n - 1)) ^ 2 * a (n - 3)) - (8 * a (n - 1) * (a (n - 2)) ^ 2)) / (a (n - 2) * a (n - 3))) : ∀ n, ∃ k : ℤ, a n = (n : ℚ) * (k : ℚ) := sorry

theorem limit_of_integral_exists (f : ℝ → ℝ) (h : ∀ x, f x = Real.sin x * Real.sin (x ^ 2)) :
    ∃ (L : ℝ), Tendsto (λ (B : ℝ) ↦ ∫ x in (0 : ℝ)..B, f x) atTop (𝓝 L) := sorry

theorem finite_group_generated_by_two_elements_odd_order_representation (G : Type*) [Group G] [Fintype G] (g h : G) (h_gen : Subgroup.closure {g, h} = ⊤) (h_odd_order : ∃ (n : ℕ), orderOf g = 2 * n + 1) : ∀ (x : G), ∃ (r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ Fintype.card G) (m n : Fin r → ℤ) (hm_range : ∀ i, m i = -1 ∨ m i = 1) (hn_range : ∀ i, n i = -1 ∨ n i = 1), x = ∏ i : Fin r, (g ^ (m i) * h ^ (n i)) := sorry

theorem count_special_tuples : 
    let n : ℕ := 64
    let N : ℕ := 2017
    let S : Set ℕ := {x | 1 ≤ x ∧ x ≤ N}
    let T (x : Fin n → ℕ) : ℕ := x 0 + x 1 + ∑ i : Fin (n - 2), (i.1 + 2) * x ⟨i.1 + 2, by omega⟩
    in Finset.card {x : Fin n → ℕ | (∀ i, x i ∈ S) ∧ (∀ i j, i < j → x i ≠ x j) ∧ ∃ k : ℤ, (T x : ℤ) = (N : ℤ) * k} = 
       ((Nat.factorial 2016) / (Nat.factorial 1953)) - ((Nat.factorial 63) * 2016) := sorry

theorem specific_L_value : Tendsto (λ (r : ℝ) => ((r ^ (-1 : ℝ)) * (∫ x in (0 : ℝ)..(π/2), (x ^ r) * Real.sin x)) / (∫ x in (0 : ℝ)..(π/2), (x ^ r) * Real.cos x)) atTop (𝓝 (2/π)) := sorry

theorem not_prime_for_positive_n (n : ℕ) (hn : n > 0) : ¬ Nat.Prime ((10 : ℕ) ^ ((10 : ℕ) ^ ((10 : ℕ) ^ n)) + (10 : ℕ) ^ ((10 : ℕ) ^ n) + (10 : ℕ) ^ n - 1) := sorry

theorem size_of_set_condition (p : ℕ) (hp : Nat.Prime p) : 
    Finset.card (Finset.filter (λ (x : ℤ × ℤ × ℤ × ℤ) => 
      let ⟨a, b, c, d⟩ := x in
      a ≥ 0 ∧ a < (p : ℤ) ∧ b ≥ 0 ∧ b < (p : ℤ) ∧ c ≥ 0 ∧ c < (p : ℤ) ∧ d ≥ 0 ∧ d < (p : ℤ) ∧
      (a + d) % (p : ℤ) = 1 % (p : ℤ) ∧ (a * d - b * c) % (p : ℤ) = 0 % (p : ℤ))
      (Finset.Ico 0 (p : ℤ) ×ˢ Finset.Ico 0 (p : ℤ) ×ˢ Finset.Ico 0 (p : ℤ) ×ˢ Finset.Ico 0 (p : ℤ))) = 
    (p ^ 2 + p) := sorry

theorem bob_winning_strategy : ∀ (n : ℕ) (hn : n ≥ 1), ∃ (strategy : (P : Set (Fin n → Fin 3)) → (V : Set (Fin n → Fin 3)) → (current_player : Bool) → (current_string : Fin n → Fin 3) → Option (Fin n → Fin 3)), ∀ (s₀ : Fin n → Fin 3) (h_s₀_zero : ∀ k, s₀ k = 0), let P : Set (Fin n → Fin 3) := Set.univ; V : Set (Fin n → Fin 3) := {s₀} in ∀ (current_player : Bool) (current_string : Fin n → Fin 3) (h_current_in_V : current_string ∈ V), (∃ (next_string : Fin n → Fin 3), legal_move current_string next_string V ∧ strategy P V current_player current_string = some next_string) ∨ (current_player = false ∧ ∀ (next_string : Fin n → Fin 3), ¬legal_move current_string next_string V) := sorry

theorem series_convergence_of_power_transform (a : ℕ → ℝ) (ha_pos : ∀ n, a n > 0) (h_converges : Summable a) : Summable (λ n => (a n) ^ ((n : ℝ) / ((n : ℝ) + 1))) := sorry

theorem guaranteed_outcome : ∃ (V : ℕ), V = 290 ∧
    (∃ (alice_strategy : (Set ℕ) → (ℕ × ℕ)) (bob_strategy : (Set ℕ) → (ℕ × ℕ)),
      ∀ (initial_state : Set ℕ), initial_state = {x | 1 ≤ x ∧ x ≤ 2022} →
      let N := 2022 in
      let squares := {x | 1 ≤ x ∧ x ≤ N} in
      let tile (i : ℕ) : ℕ × ℕ := (i, i + 1) in
      let valid_tile (i : ℕ) : Prop := 1 ≤ i ∧ i ≤ N - 1 in
      let placement := ∅ : Set (ℕ × ℕ) in
      let game_state := initial_state in
      let move (p : Set (ℕ × ℕ)) (s : Set ℕ) (t : ℕ × ℕ) : Set (ℕ × ℕ) × Set ℕ :=
        (p ∪ {t}, s \ ({t.1} ∪ {t.2})) in
      let end_condition (s : Set ℕ) : Prop :=
        ¬∃ (i : ℕ), valid_tile i ∧ i ∈ s ∧ (i + 1) ∈ s in
      let alice_turn : Bool := true in
      let rec play (p : Set (ℕ × ℕ)) (s : Set ℕ) (turn : Bool) : ℕ :=
        if end_condition s then Finset.card (s.filter (λ x => x ∈ squares)).toFinset
        else
          let chosen_tile := if turn then alice_strategy s else bob_strategy s in
          let (new_p, new_s) := move p s chosen_tile in
          play new_p new_s (¬turn) in
      let outcome := play placement game_state alice_turn in
      outcome ≥ V) := sorry

theorem sequence_condition (n : ℕ) (hn : n > 0) (c : ℝ) (x : ℕ → ℝ) (hx0 : x 0 = 0) (hx1 : x 1 = 1) (hrec : ∀ k : ℕ, x (k + 2) = ((c * x (k + 1)) - ((n : ℝ) - (k : ℝ)) * x k) / ((k : ℝ) + 1)) (hc_max : IsGreatest {c' : ℝ | ∀ x' : ℕ → ℝ, x' 0 = 0 → x' 1 = 1 → (∀ k, x' (k + 2) = ((c' * x' (k + 1)) - ((n : ℝ) - (k : ℝ)) * x' k) / ((k : ℝ) + 1)) → x' (n + 1) = 0} c) : ∀ k, k ∈ Finset.Icc 1 n → x k = (Nat.choose (n - 1) (k - 1) : ℝ) := sorry

theorem sum_arccot_eq_pi_div_two : 
    let π := Real.pi
    let Arccot : ℝ → ℝ := fun t => if h : 0 ≤ t then Classical.choose (exists_unique_arccot t h) else 0
    have hArccot_prop : ∀ (t : ℝ) (ht : 0 ≤ t), 0 < Arccot t ∧ Arccot t ≤ π / 2 ∧ Real.cot (Arccot t) = t := by
      intro t ht
      exact Classical.choose_spec (exists_unique_arccot t ht)
    have exists_unique_arccot : ∀ (t : ℝ) (ht : 0 ≤ t), ∃! θ : ℝ, 0 < θ ∧ θ ≤ π / 2 ∧ Real.cot θ = t := by
      sorry
    have summable_arccot : Summable fun n : ℕ => Arccot ((n : ℝ) ^ 2 + (n : ℝ) + 1) := by
      sorry
    ∑' n : ℕ, Arccot ((n : ℝ) ^ 2 + (n : ℝ) + 1) = π / 2 := sorry

theorem function_identity (f g h : ℝ → ℝ) (h_f : ∀ x : ℝ, f x = (h (x + 1) + h (x - 1)) / 2) (h_g : ∀ x : ℝ, g x = (h (x + 4) + h (x - 4)) / 2) : ∀ x : ℝ, h x = ((g x - f (x - 3)) + f (x - 1) + f (x + 1)) - f (x + 3) := sorry

theorem exists_linear_combination_of_product (n : ℕ) (hn : n > 0) : 
    ∃ (N : ℕ) (c : Fin N → ℚ) (a : Fin N → Fin n → ℤ) (ha : ∀ i j, a i j ∈ ({-1, 0, 1} : Set ℤ)), 
    ∀ (x : Fin n → ℝ), ∏ j, x j = ∑ i, (c i : ℝ) * (∑ j, (a i j : ℝ) * x j) ^ n := sorry

theorem goal_theorem : M n₀ = 1 / 4040 := sorry

theorem integer_sequence : ∀ (u : ℕ → ℚ) (h0 : u 0 = 1) (h1 : u 1 = 1) (h2 : u 2 = 1) (det_eq : ∀ n, ((u n) * (u (n + 3))) - ((u (n + 1)) * (u (n + 2))) = (Nat.factorial n : ℚ)), ∀ n, ∃ (k : ℤ), u n = (k : ℚ) := sorry

theorem specific_alpha_beta_limit : Filter.Tendsto (λ (N : ℕ) => (Real.ofNat (S N)) / ((Real.ofNat N) ^ ((3 : ℝ)/4))) Filter.atTop (𝓝 ((4 : ℝ)/3)) := sorry

theorem sum_series_eq_ratio (x : ℝ) (hx_pos : 0 < x) (hx_lt_one : x < 1) : 
    (∑' n : ℕ, (x ^ (2 ^ n)) / (1 - x ^ (2 ^ (n + 1)))) = x / (1 - x) := sorry

theorem limit_ratio_zero (a : ℕ → ℕ) (hpos : ∀ n, a n > 0) (hconv : Summable fun n : ℕ => (1 : ℝ) / (a n : ℝ)) (b : ℕ → ℕ) (hb_def : ∀ n, b n = Finset.card (Finset.filter (fun k => a k ≤ n) Finset.univ)) : Filter.Tendsto (fun n : ℕ => (b n : ℝ) / (n : ℝ)) Filter.atTop (𝓝 0) := sorry

theorem sum_one_div_lcm_converges (a : ℕ → ℕ) (ha_pos : ∀ n, a n > 0) (ha_strictMono : ∀ n, a n < a (n + 1)) : 
    ∃ L : ℝ, HasSum (λ n : ℕ => 1 / (Nat.lcm (Finset.sup (Finset.Icc 1 (n + 1)) a) : ℝ)) L := sorry

theorem set_S_contains_all_positive_integers (S : Set ℕ) (hS_nonempty : S.Nonempty) (hS_condition : ∀ n, n ∈ S → ∀ d, 0 < d → (d ∣ (2025 ^ n - 15 ^ n)) → d ∈ S) : ∀ k, 0 < k → k ∈ S := sorry

theorem rational_subset_positive_iff (S : Set ℚ) (h_add : ∀ a b ∈ S, a + b ∈ S) (h_mul : ∀ a b ∈ S, a * b ∈ S) (h_trich : ∀ r : ℚ, (r ∈ S ∧ (-r) ∉ S) ∨ ((-r) ∈ S ∧ r ∉ S) ∨ r = 0) : ∀ q : ℚ, q ∈ S ↔ q > 0 := sorry

example : ∃ (S : Type) (op : S → S → S), (∀ (a b c d : S), op (op a b) (op c d) = op a d) ∧ (∀ (a : S), op a a = a) ∧ (∃ (a b : S), op a b = a ∧ a ≠ b) ∧ (∃ (a b : S), op a b ≠ a) := sorry

theorem size_of_maximal_intersecting_family (S : Finset α) (P : Finset (Finset α)) (hS_finite : S.Finite := by exact Finset.finite_toSet S) :
    (∀ A ∈ P, A ⊆ S) ∧
    (∀ A ∈ P, ∀ B ∈ P, A ≠ B → (A ∩ B).Nonempty) ∧
    (¬∃ Q : Finset (Finset α), P ⊂ Q ∧ (∀ A ∈ Q, A ⊆ S) ∧ (∀ A ∈ Q, ∀ B ∈ Q, A ≠ B → (A ∩ B).Nonempty)) →
    Finset.card P = 2 ^ (Finset.card S - 1) := sorry

theorem tan_roots_difference_estimate (π : ℝ) (hπ : π = Real.pi) (r : ℕ → ℝ) (hpos : ∀ n, 0 < r n) (htan_eq : ∀ n, Real.tan (r n) = r n) (horder : ∀ n, r n = Nat.find (fun x : ℝ => Real.tan x = x ∧ 0 < x) (by
    have := exists_pos_tan_eq_self (n := n)
    exact this)) : ∀ (n : ℕ) (hn : n ≥ 1), 0 < r (n + 1) - r n - π ∧ r (n + 1) - r n - π < 1 / (((n : ℝ) ^ 2 + n) * π) := sorry

theorem sum_of_products_plus_one (n : ℕ) (hcomp : ¬ Nat.Prime n) (hpos : n > 1) : 
    ∃ (x y z : ℕ), n = (x * y) + (x * z) + (y * z) + 1 := sorry

theorem exists_constant_bound_for_polynomial_at_zero : ∃ (C : ℝ), ∀ (p : Polynomial ℝ) (hdeg : p.natDegree = 1999), |p.eval 0| ≤ C * (∫ x in (-1 : ℝ)..(1 : ℝ), |p.eval x|) := sorry

theorem exists_sequence_of_closed_discs : ∃ (c : ℕ → ℝ × ℝ) (r : ℕ → ℝ) (D : ℕ → Set (ℝ × ℝ)),
  (∀ n, r n > 0) ∧
  (∀ n, D n = {x : ℝ × ℝ | Real.dist x (c n) ≤ r n}) ∧
  (¬∃ (p : ℝ × ℝ), Filter.Tendsto c Filter.atTop (nhds p)) ∧
  (Summable fun n : ℕ => π * (r n) ^ 2) ∧
  (∀ (L : Set (ℝ × ℝ)), (∃ (a b : ℝ), (a, b) ≠ (0, 0) ∧ L = {x : ℝ × ℝ | a * x.1 + b * x.2 = 0}) → ∃ n, Set.Nonempty (L ∩ D n)) := sorry

theorem integral_inequality :
    let S : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1} in
    ∀ (f : S → ℝ) (hf : ∀ p : S, ContinuousAt f p),
    let g : ℝ → ℝ := λ y => if hy : (0 : ℝ) ≤ y ∧ y ≤ 1 then ∫ x in (0:ℝ)..1, f (⟨(x, y), by
        intro h
        rcases h with ⟨hx_left, hx_right, hy_left, hy_right⟩
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩) else 0 in
    let h : ℝ → ℝ := λ x => if hx : (0 : ℝ) ≤ x ∧ x ≤ 1 then ∫ y in (0:ℝ)..1, f (⟨(x, y), by
        intro h
        rcases h with ⟨hx_left, hx_right, hy_left, hy_right⟩
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩) else 0 in
    (∫ y in (0:ℝ)..1, (g y) ^ 2) + (∫ x in (0:ℝ)..1, (h x) ^ 2) ≤ (∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, f (⟨(x, y), by
        intro h
        rcases h with ⟨hx_left, hx_right, hy_left, hy_right⟩
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩)) ^ 2 + (∫ y in (0:ℝ)..1, ∫ x in (0:ℝ)..1, (f (⟨(x, y), by
        intro h
        rcases h with ⟨hx_left, hx_right, hy_left, hy_right⟩
        exact ⟨by linarith, by linarith, by linarith, by linarith⟩⟩)) ^ 2) := sorry

theorem exists_sequence_with_polynomials_having_distinct_real_roots : ∃ (a : ℕ → ℝ) (h : ∀ n, a n ≠ 0), ∀ (n : ℕ) (hn : n ≥ 1), ∃ (roots : Finset ℝ) (hroots : roots.card = n), ∀ (x : ℝ), (∑ k in Finset.range (n + 1), a k * x ^ k) = 0 ↔ x ∈ roots := sorry

theorem set_size_formula (r s : ℕ) (hr : r > 0) (hs : s > 0) : 
    let L := (3 : ℕ) ^ r * (7 : ℕ) ^ s
    let S : Set (ℕ × ℕ × ℕ × ℕ) := {x | ∃ (a b c d : ℕ), x = (a, b, c, d) ∧ a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ Nat.lcm (Nat.lcm a b) c = L ∧ Nat.lcm (Nat.lcm a b) d = L ∧ Nat.lcm (Nat.lcm a c) d = L ∧ Nat.lcm (Nat.lcm b c) d = L}
    in Finset.card (S.toFinset) = ((1 + 4 * r + 6 * (r ^ 2)) * (1 + 4 * s + 6 * (s ^ 2))) := sorry

theorem series_equality : S = (Real.log 2) ^ 2 := sorry

theorem no_potential_for_G : ¬∃ (F : ℝ × ℝ × ℝ \ {(0,0,0)} → ℝ × ℝ × ℝ) (M N P : ℝ × ℝ × ℝ → ℝ),
    (∀ (x y z : ℝ), (x, y, z) ≠ (0, 0, 0) → F (x, y, z) = (M (x, y, z), N (x, y, z), P (x, y, z))) ∧
    (∀ (x y z : ℝ), (x, y, z) ≠ (0, 0, 0) → ContinuousAt (fun x' => M (x', y, z)) x ∧
      ContinuousAt (fun y' => M (x, y', z)) y ∧
      ContinuousAt (fun z' => M (x, y, z')) z ∧
      ContinuousAt (fun x' => N (x', y, z)) x ∧
      ContinuousAt (fun y' => N (x, y', z)) y ∧
      ContinuousAt (fun z' => N (x, y, z')) z ∧
      ContinuousAt (fun x' => P (x', y, z)) x ∧
      ContinuousAt (fun y' => P (x, y', z)) y ∧
      ContinuousAt (fun z' => P (x, y, z')) z) ∧
    (∀ (x y z : ℝ), (x, y, z) ≠ (0, 0, 0) →
      (fun (x' : ℝ) => ∂/∂x' (N (x', y, z)) - ∂/∂y' (M (x, y', z)) |_{x'=x, y'=y} = 0) ∧
      (fun (y' : ℝ) => ∂/∂y' (P (x, y', z)) - ∂/∂z' (N (x, y, z')) |_{y'=y, z'=z} = 0) ∧
      (fun (z' : ℝ) => ∂/∂z' (M (x, y, z')) - ∂/∂x' (P (x', y, z)) |_{z'=z, x'=x} = 0)) ∧
    (∀ (x y : ℝ), (x^2 + 4 * y^2) ≠ 0 → F (x, y, 0) = ((-y) / (x^2 + 4 * y^2), x / (x^2 + 4 * y^2), 0)) := sorry

theorem probability_condition_square (L : ℝ) (hL : L > 0) : 
    let square : Set (ℝ × ℝ) := {p | -L/2 ≤ p.1 ∧ p.1 ≤ L/2 ∧ -L/2 ≤ p.2 ∧ p.2 ≤ L/2} in
    let center_distance (p : ℝ × ℝ) : ℝ := Real.sqrt (p.1^2 + p.2^2) in
    let nearest_edge_distance (p : ℝ × ℝ) : ℝ := min (L/2 - |p.1|) (L/2 - |p.2|) in
    let condition_set : Set (ℝ × ℝ) := {p | p ∈ square ∧ center_distance p < nearest_edge_distance p} in
    let total_area : ℝ := L^2 in
    let condition_area : ℝ := ((4 * Real.sqrt 2) - 5) / 3 * L^2 in
    condition_area / total_area = ((4 * Real.sqrt 2) - 5) / 3 := sorry

theorem line_intersection_condition (L1 L2 : Set (ℝ × ℝ)) (hL1 : IsAffineSubspace ℝ L1) (hL2 : IsAffineSubspace ℝ L2) (h_dim1 : finrank ℝ (Submodule.span ℝ L1) = 1) (h_dim2 : finrank ℝ (Submodule.span ℝ L2) = 1) (h_ne : L1 ≠ L2) : 
    (∃ p, p ∈ L1 ∧ p ∈ L2) ↔ 
    (∀ (λ : ℝ) (hλ : λ ≠ 0) (P : ℝ × ℝ) (hP1 : P ∉ L1) (hP2 : P ∉ L2), 
      ∃ (A1 : ℝ × ℝ) (A2 : ℝ × ℝ), A1 ∈ L1 ∧ A2 ∈ L2 ∧ (A2.1 - P.1, A2.2 - P.2) = λ • (A1.1 - P.1, A1.2 - P.2)) := sorry

theorem no_integer_factor_of_Mersenne_minus_one (n : ℤ) (hn : n > 1) : ¬∃ (k : ℤ), (2 ^ n - 1) = n * k := sorry

theorem exists_polynomial_H (n : ℕ) (hn : n > 0) : ∃ (H : Polynomial ℤ), (∀ (x y : ℝ), Polynomial.eval₂ (algebraMap ℤ ℝ) (P x y, Q x y) H = F_n x y) ∨ (∀ (x y : ℝ), Polynomial.eval₂ (algebraMap ℤ ℝ) (P x y, Q x y) H = G_n x y) := sorry

theorem group_commutativity_condition (m n : ℕ) (hm : m > 0) (hn : n > 0) (hcoprime : Nat.Coprime m n) (G : Type*) [Group G] (g h : G) :
    (let a : ℕ → ℤ := fun k => (Int.floor ((m : ℤ) * (k : ℤ) / (n : ℤ))) - (Int.floor ((m : ℤ) * ((k : ℤ) - 1) / (n : ℤ))) in
    (Finset.prod (Finset.Icc 1 n) fun k => g * (h ^ (a k))) = 1) → g * h = h * g := sorry

theorem exists_bound_on_min_pairwise_F (F : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (hF_zero_diag : ∀ (u : ℝ), F (u, u) = 0) (hg_pos : ∀ (x : ℝ), g x > 0) (hg_bound : ∀ (x : ℝ), (x ^ 2) * g x ≤ 1) (hgrad_parallel : ∀ (u v : ℝ), ∇ F (u, v) = 0 ∨ ∃ (λ : ℝ), ∇ F (u, v) = λ • (g u, -g v)) (hF_smooth : ContDiff ℝ 2 F) (hg_smooth : ContDiff ℝ 2 g) (n : ℕ) (hn : n ≥ 2) (x : ℕ → ℝ) : ∃ (C : ℝ), (Finset.inf' (Finset.filter (λ (ij : ℕ × ℕ) => ij.1 ≠ ij.2) (Finset.range (n + 1) ×ˢ Finset.range (n + 1))) (by simp) (λ (ij : ℕ × ℕ) => |F (x ij.1, x ij.2)|)) ≤ C / n := sorry

theorem f_lower_bound : ∀ (x : ℝ), 0 ≤ x ∧ x < 1 → (let L : ℝ := 4/7; let f : ℝ → ℝ := λ x => ∑' (n : ℕ), if 1 ≤ n ∧ Int.even (⌊(n : ℝ) * x⌋.toInt) then (1 : ℝ) / ((2 : ℝ) ^ n) else 0; f x ≥ L) := sorry

theorem set_equality : {n : ℕ | ∃ (q : ℤ), f n = 11 * q} = {n : ℕ | ∃ (k : ℤ), n = 6 * k + 1} := sorry

theorem finite_common_zeros_of_integrals (P : ℝ → ℝ) (hP : Polynomial P) (hP_nonconst : ¬ Polynomial.constant P) :
    Set.Finite {x : ℝ | (fun x : ℝ => ∫ t in (0 : ℝ)..x, P t * Real.sin t) x = 0 ∧ (fun x : ℝ => ∫ t in (0 : ℝ)..x, P t * Real.cos t) x = 0} := sorry

theorem tangent_line_condition (m n u v a b : ℝ) (hm : m > 1) (hn : (1 / m) + (1 / n) = 1) (hu : u ≥ 0) (hv : v ≥ 0) (hv_ne_zero : v ≠ 0) (ha_nonneg : a ≥ 0) (hb_nonneg : b ≥ 0) (h_curve_eq : a ^ m + b ^ m = 1) (h_line_eq : u * a + v * b = 1) (h_tangent : ∀ (x y : ℝ), (x ^ m + y ^ m = 1) → (u * x + v * y = 1) → (x = a ∧ y = b)) : u ^ n + v ^ n = 1 := sorry

theorem sign_patterns_cardinality : 
    let i : ℕ := 0 in
    let indices : Finset ℕ := {1, 2, 3, 4} in
    let a : ℕ → ℝ := λ _ => 0 in
    let b : ℕ → ℝ := λ _ => 0 in
    let x : ℕ → ℝ := λ _ => 0 in
    let S : Set (ℕ → ℝ) := {x | 
      (a 1 * b 2 - a 2 * b 1) ≠ 0 ∧
      (a 1 * x 1 + a 2 * x 2 + a 3 * x 3 + a 4 * x 4) = 0 ∧
      (b 1 * x 1 + b 2 * x 2 + b 3 * x 3 + b 4 * x 4) = 0 ∧
      ∀ i ∈ indices, x i ≠ 0} in
    let T : Set (ℕ → ℤ) := {s | ∃ x ∈ S, ∀ i ∈ indices, s i = Int.sign (x i)} in
    Finset.card (T.toFinset) = 8 := sorry

theorem rational_integral_sum : ∃ (r : ℚ), (∫ x in (-100 : ℝ)..(-10 : ℝ), ((fun (x : ℝ) => ((x ^ 2 - x) / (x ^ 3 - 3 * x + 1)) ^ 2) x)) + (∫ x in ((1/101 : ℝ))..((1/11 : ℝ)), ((fun (x : ℝ) => ((x ^ 2 - x) / (x ^ 3 - 3 * x + 1)) ^ 2) x)) + (∫ x in ((101/100 : ℝ))..((11/10 : ℝ)), ((fun (x : ℝ) => ((x ^ 2 - x) / (x ^ 3 - 3 * x + 1)) ^ 2) x)) = (r : ℝ) := sorry

theorem permutation_count_mod_condition (n k : ℕ) (hn_pos : n > 0) (hk_pos : k > 0) :
    let S : Finset ℕ := Finset.Icc 1 n
    let permutations_set : Finset (ℕ → ℕ) :=
      Finset.filter (fun σ : ℕ → ℕ => ∀ i, i ∈ S → |σ i - i| ≤ k)
        (Finset.filter (Function.Bijective (fun i : S => σ i)) Finset.univ)
    in (permutations_set.card % 2 = 1) ↔ (n % (2 * k + 1) = 0 ∨ n % (2 * k + 1) = 1) := sorry

theorem area_sum_arc_length_relation (s : Set (ℝ × ℝ)) (h_arc : IsArc s) (h_quadrant : s ⊆ {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1^2 + p.2^2 = 1}) (A B L : ℝ) 
    (hA : A = volume {p : ℝ × ℝ | (p.1, p.2) ∈ s ∧ p.2 ≥ 0 ∧ p.2 ≤ Real.sqrt (1 - p.1^2)})
    (hB : B = volume {p : ℝ × ℝ | (p.1, p.2) ∈ s ∧ p.1 ≥ 0 ∧ p.1 ≤ Real.sqrt (1 - p.2^2)})
    (hL : L = arcLength s) : A + B = π/4 - L/2 := sorry

theorem derivative_condition : ∀ (n : ℕ) (a : ℕ → ℂ) (h : a n ≠ 0) (p : ℂ → ℂ) (hp : ∀ z, p z = ∑ k in Finset.range (n + 1), a k * z ^ k) (hroot : ∀ z : ℂ, p z = 0 → Complex.abs z = 1) (g : ℂ → ℂ) (hg : ∀ z, g z = p z / (z ^ (n / 2))) (g' : ℂ → ℂ) (hg' : ∀ z, g' z = deriv g z), ∀ z : ℂ, g' z = 0 → Complex.abs z = 1 := sorry

theorem equality_of_functions_on_interval : 
    ∀ (x : ℝ), x ∈ Set.Icc (0 : ℝ) 1 → f x = g x := sorry

theorem sum_of_distances_maximized_by_regular_pentagon : 
    let n : ℕ := 5 in
    let S : Set (ℝ × ℝ) := {p₁, p₂, p₃, p₄, p₅} in
    let points : Fin n → ℝ × ℝ := λ i => match i with
      | 0 => p₁ | 1 => p₂ | 2 => p₃ | 3 => p₄ | 4 => p₅ in
    let d : (ℝ × ℝ) → (ℝ × ℝ) → ℝ := λ x y => Real.sqrt (((x.1 - y.1) ^ 2) + ((x.2 - y.2) ^ 2)) in
    let Σ : (Fin n → ℝ × ℝ) → ℝ := λ pts => 
      ∑ i : Fin n, ∑ j : Fin n, if i.val < j.val then d (pts i) (pts j) else 0 in
    ∀ (p₁ p₂ p₃ p₄ p₅ : ℝ × ℝ), 
      (∀ i : Fin n, (points i).1 ^ 2 + (points i).2 ^ 2 = 1) → 
      Σ points ≤ Σ (λ k => (Real.cos (2 * π * (k : ℝ) / n), Real.sin (2 * π * (k : ℝ) / n))) := sorry

theorem tetrahedron_count_equality : 
    let positiveIntegers : Set ℕ := {m | 0 < m} in
    let N_set1 : Set ℕ := {N | ∃ m ∈ positiveIntegers, N = 3 * (m ^ 2)} in
    let N_set2 : Set ℕ := {N | ∃ (m : ℕ) (h : 0 < m) (S : Set (ℤ × ℤ × ℤ)), 
        S = {(x, y, z) | x^2 + y^2 + z^2 = (3 * (m ^ 2) : ℤ)} ∧
        ∃ (T : Set (ℤ × ℤ × ℤ)) (hT : T ⊆ S) (hcard : Finset.card (T : Finset (ℤ × ℤ × ℤ)).val = 4) 
            (hdistinct : Set.InjOn (fun p : ℤ × ℤ × ℤ => p) T) 
            (hregular : ∃ (a b : ℤ × ℤ × ℤ) (hab : a ∈ T ∧ b ∈ T ∧ a ≠ b), 
                ∀ (c d : ℤ × ℤ × ℤ), c ∈ T → d ∈ T → c ≠ d → 
                dist (c : ℤ × ℤ × ℤ) d = dist a b), 
        N = 3 * (m ^ 2)} in
    Set.ncard N_set1 = Set.ncard N_set2 := sorry

theorem exists_linear_function (n : ℕ) (hn : n > 0) (f : ℝ → ℝ) (hf : Differentiable ℝ f) 
    (h : ∀ (x : ℝ) (n : ℕ), n > 0 → deriv f x = ((f (x + (n : ℝ)) - f x) / (n : ℝ))) : 
    ∃ (c d : ℝ), ∀ (x : ℝ), f x = c * x + d := sorry

theorem sequence_count_bound (n : ℤ) (hn : n ≥ 2) : 
    let S : Set (Fin (n - 1).toNat → ℤ) := {s | ∀ i : Fin (n - 1).toNat, s i = (1 : ℤ) ∨ s i = (-1 : ℤ)} in
    let f (s : Fin (n - 1).toNat → ℤ) : ℕ := 
      Finset.card (Finset.filter (fun (a : Equiv.Perm (Fin n.toNat)) => 
        ∀ i : Fin (n - 1).toNat, s i * ((a (Fin.succ i) : ℤ) - (a i : ℤ)) > 0) 
        (Finset.univ : Finset (Equiv.Perm (Fin n.toNat)))) in
    let s_alt (i : Fin (n - 1).toNat) : ℤ := (-1 : ℤ) ^ ((i : ℕ) + 1) in
    ∀ s ∈ S, f s ≤ f s_alt ∧ (f s = f s_alt ↔ 
      (∀ i : Fin (n - 1).toNat, s i = (-1 : ℤ) ^ ((i : ℕ) + 1)) ∨ 
      (∀ i : Fin (n - 1).toNat, s i = (-1 : ℤ) ^ (i : ℕ))) := sorry

theorem partition_sum_condition_implies_v_a_eq_one_and_v_b_even (v : ℤ × ℤ) (hv : v ∈ {p : ℤ × ℤ | 0 ≤ p.1 ∧ p.1 ≤ 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 100}) : 
    ∃ (A B : Set (ℤ × ℤ)) (hA : A ⊆ {p : ℤ × ℤ | 0 ≤ p.1 ∧ p.1 ≤ 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 100} \ {v}) 
      (hB : B ⊆ {p : ℤ × ℤ | 0 ≤ p.1 ∧ p.1 ≤ 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 100} \ {v}), 
      A ∩ B = ∅ ∧ A ∪ B = {p : ℤ × ℤ | 0 ≤ p.1 ∧ p.1 ≤ 2 ∧ 0 ≤ p.2 ∧ p.2 ≤ 100} \ {v} ∧ 
      Finset.card (A.toFinset) = Finset.card (B.toFinset) ∧ 
      (∑ x in A.toFinset, (x.1 + x.2)) = (∑ x in B.toFinset, (x.1 + x.2)) → 
      v.1 = 1 ∧ 0 ≤ v.2 ∧ v.2 ≤ 100 ∧ ∃ (k : ℤ), v.2 = 2 * k := sorry

theorem exists_c_such_that_f_has_form : ∃ (c : ℝ), c ≥ 0 ∧ ∀ (x : ℝ), x > 0 → f x = 1 / (1 + c * x) := sorry

theorem thousandth_digit_of_sqrt_is_one : 
    ∃ (N : ℕ) (hpos : N > 0) (hdigits : Nat.log 10 N + 1 = 1998) (hdigits_one : ∀ i : ℕ, 1 ≤ i → i ≤ 1998 → 
      (Nat.digits 10 N).get ⟨i - 1, by omega⟩ = 1), 
    let A := Real.sqrt (N : ℝ) in 
    let fractional_part := A - ⌊A⌋ in
    let thousandth_digit := ⌊fractional_part * 10 ^ 1000⌋ % 10 in
    thousandth_digit = 1 := sorry

theorem integral_polynomial_approx (T : ℝ) (hT : T > 0) (H : ℝ → ℝ) (hH : Polynomial ℝ H) (hdeg : Polynomial.degree (Polynomial.ofFun H) ≤ 3) :
    (1 / (2 * T)) * ∫ x in -T..T, H x = ((H (-T / Real.sqrt 3)) + H (T / Real.sqrt 3)) / 2 := sorry

theorem supremum_of_s_ratio_eq_one_over_k_factorial : 
    let k : ℕ := 1 in
    let n : ℕ := k in
    let s : ℕ × ((Fin n) → ℝ) → ℝ := λ ⟨m, a⟩ => 
      ∑ I : Finset (Fin n) in Finset.powersetCard m Finset.univ, ∏ i in I, a i in
    let candidate_set : Set ℝ := 
      { x : ℝ | ∃ (n : ℕ) (hn : n ≥ k) (a : Fin n → ℝ) (ha : ∀ i, a i > 0), 
          x = s (k, a) / ((s (1, a)) ^ k) } in
    sSup candidate_set = 1 / (Nat.factorial k) := sorry

theorem exists_subset_with_lower_bound (n : ℕ) (f : ℝ → ℝ) (h_int : IntegrableOn f (Set.Icc (0 : ℝ) 1) volume) 
    (h_zero_integrals : ∀ i : ℤ, i ∈ Finset.Icc (0 : ℤ) ((n : ℤ) - 1)) → ∫ x in (0 : ℝ)..1, (x : ℝ) ^ (i : ℕ) * f x ∂volume = 0)
    (h_one_integral : ∫ x in (0 : ℝ)..1, (x : ℝ) ^ n * f x ∂volume = 1) :
    ∃ S : Set ℝ, S ⊆ Set.Icc (0 : ℝ) 1 ∧ 0 < volume S ∧ ∀ x ∈ S, |f x| ≥ (2 : ℝ) ^ n * ((n : ℝ) + 1) := sorry

theorem exists_square_vertex (A B C : ℤ × ℤ) (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) : 
    ∃ (D : ℤ × ℤ), D ≠ A ∧ D ≠ B ∧ D ≠ C ∧ 
    let vertices : Finset (ℤ × ℤ) := {A, B, C, D} in 
    vertices.card = 4 ∧ 
    let d (X Y : ℤ × ℤ) : ℝ := Real.sqrt (((X.1 : ℝ) - (Y.1 : ℝ)) ^ 2 + ((X.2 : ℝ) - (Y.2 : ℝ)) ^ 2) in
    let area (X Y Z : ℤ × ℤ) : ℝ := (1/2 : ℝ) * |((X.1 : ℝ) * ((Y.2 : ℝ) - (Z.2 : ℝ)) + (Y.1 : ℝ) * ((Z.2 : ℝ) - (X.2 : ℝ)) + (Z.1 : ℝ) * ((X.2 : ℝ) - (Y.2 : ℝ)))| in
    (d A B + d B C) ^ 2 < 8 * area A B C + 1 → 
    ∃ (perm : Equiv.Perm (ℤ × ℤ)), perm '' vertices = vertices ∧ 
    ∀ (X Y : ℤ × ℤ), X ∈ vertices → Y ∈ vertices → d (perm X) (perm Y) = d X Y ∧ 
    (X ≠ Y → (perm X ≠ perm Y) ∧ (perm (perm X) = X)) := sorry

theorem coefficient_sum_bound (k : ℕ) (hk : 0 ≤ k) : 
    let a : ℕ × ℕ → ℕ := λ ⟨m, n⟩ ↦ Polynomial.coeff (ℕ) ((1 + Polynomial.X + Polynomial.X ^ 2) ^ m) n
    let S : ℕ → ℤ := λ k ↦ ∑ i in Finset.Icc 0 (⌊(2 * k : ℝ) / 3⌋.toNat), (-1 : ℤ) ^ i * (a (k - i, i) : ℤ)
    in (0 : ℤ) ≤ S k ∧ S k ≤ 1 := sorry

theorem sum_of_interval_products_eq_one_third : 
    let I : Set ℝ := Set.Ioo (0 : ℝ) (1 : ℝ) in
    ∀ (x : ℕ → ℝ) (hx_inj : ∀ i j : ℕ, i ≠ j → x i ≠ x j) (hx_dense : Dense (x '' Set.univ ∩ I)) 
    (hx_partition : ∀ n : ℕ, n ≥ 1 → 
      let points := Finset.image (fun k : ℕ => x k) (Finset.range n) in
      let intervals := Finset.powersetCard (n - 1) points in
      ∀ (interval : Finset ℝ) (hinterval : interval ∈ intervals), 
        ∃! (subinterval : Set ℝ), subinterval ⊆ I ∧ 
          Set.OrdConnected subinterval ∧ 
          x n ∈ subinterval ∧ 
          (∀ y ∈ subinterval, y ∉ points)) 
    (hx_placement : ∀ n : ℕ, n ≥ 1 → 
      ∃ (subinterval : Set ℝ), subinterval ⊆ I ∧ 
        Set.OrdConnected subinterval ∧ 
        x n ∈ subinterval ∧ 
        (∀ y ∈ subinterval, y ∉ Finset.image (fun k : ℕ => x k) (Finset.range n))) 
    (a b : ℕ → ℝ) 
    (ha_def : ∀ n : ℕ, n ≥ 1 → 
      let left_endpoint := sSup {y : ℝ | y < x n ∧ y ∈ I ∧ 
        (∀ k : ℕ, k < n → x k ≠ y)} in
      a n = x n - left_endpoint) 
    (hb_def : ∀ n : ℕ, n ≥ 1 → 
      let right_endpoint := sInf {y : ℝ | y > x n ∧ y ∈ I ∧ 
        (∀ k : ℕ, k < n → x k ≠ y)} in
      b n = right_endpoint - x n), 
    ∑' (n : ℕ), (if n ≥ 1 then a n * b n * (a n + b n) else 0) = (1/3 : ℝ) := sorry

theorem power_series_coefficient_zero_set_cardinality (a b : ℝ) (ha : a > 0) (hb : b > 0) :
    let f : ℝ → ℝ := λ x => Real.exp (a * x) * Real.cos (b * x) in
    let c : ℕ → ℝ := λ n => (iteratedDeriv n f 0) / (Nat.factorial n : ℝ) in
    (Finset.card (Finset.filter (λ n => c n = 0) Finset.univ : Finset ℕ) = 0) ∨
    Set.Infinite {n : ℕ | c n = 0} := sorry

theorem finite_group_union_of_three_proper_subgroups : ∃ (G : Type) [Group G] [Fintype G], ∃ (H1 H2 H3 : Subgroup G), H1 ≠ ⊤ ∧ H2 ≠ ⊤ ∧ H3 ≠ ⊤ ∧ (∀ x : G, x ∈ H1 ∨ x ∈ H2 ∨ x ∈ H3) := sorry

theorem exists_K_such_that_for_all_k_gt_K_gcd_of_2m_plus_one_and_2n_plus_one_is_one (m₀ n₀ : ℕ) (h_m₀_ne_n₀ : m₀ ≠ n₀) (h_m₀_pos : m₀ > 0) (h_n₀_pos : n₀ > 0) (m n : ℕ → ℕ) (h_rec : ∀ k ≥ 1, (m k : ℚ) / (n k : ℚ) = ((2 * m (k - 1) + 1 : ℚ) / (2 * n (k - 1) + 1 : ℚ))) (h_coprime : ∀ k ≥ 1, Nat.gcd (m k) (n k) = 1) : ∃ K : ℕ, ∀ k > K, Nat.gcd (2 * m k + 1) (2 * n k + 1) = 1 := sorry

theorem f_of_38 : f 38 = 1444 := sorry

theorem exists_polynomial_with_property (n : ℤ) (hn : n ≥ 2) : ∃ (P : ℤ[X] → ℤ[X] → ℤ[X] → ℤ[X]), ∀ (x : ℤ), x = P (x ^ n) (x ^ (n + 1)) (x + x ^ (n + 2)) := sorry

theorem exists_polynomial_for_f (k m : ℕ) (hk : k > 0) (hm : m > 0) :
    ∃ (P : Polynomial ℕ), ∀ (n : ℕ) (hn : n > 0), f k m n = Polynomial.eval n P := sorry

theorem exists_int_m_and_not_exists_m_prime (b : ℕ → ℤ) (h0 : b 0 = 0) (hrec : ∀ n : ℕ, b (n + 1) = 2 * (b n) ^ 2 + b n + 1) (k : ℕ) (hk : k ≥ 1) : 
    (∃ m : ℤ, b (2 ^ (k + 1)) - 2 * b (2 ^ k) = (2 : ℤ) ^ (2 * k + 2) * m) ∧ 
    ¬∃ m' : ℤ, b (2 ^ (k + 1)) - 2 * b (2 ^ k) = (2 : ℤ) ^ (2 * k + 3) * m' := sorry

theorem mediocre_subset_property (n : ℕ) (hn : n > 0) : 
    ∀ (S : Set ℕ) (hS : S ⊆ Finset.Icc 1 n), 
    (∀ a ∈ S, ∀ b ∈ S, (a + b) % 2 = 0 → ((a + b) / 2) ∈ S) → 
    let A : ℕ → ℕ := λ m => Fintype.card {S : Finset ℕ // S ⊆ Finset.Icc 1 m ∧ ∀ a ∈ S, ∀ b ∈ S, (a + b) % 2 = 0 → ((a + b) / 2) ∈ S}
    in A 3 = 7 → 
    (∀ n' : ℕ, n' > 0 → (A (n' + 2) - 2 * A (n' + 1) + A n' = 1) → 
    ∃ k : ℕ, n' = 2 ^ k - 1) := sorry

theorem exists_bound_on_f (f : ℝ → ℝ) (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f)) (g : ℝ → ℝ) (hg_nonneg : ∀ x, 0 ≤ g x) (h_eq : ∀ x, f x + deriv (deriv f) x = (-x) * g x * deriv f x) : ∃ M : ℝ, ∀ x, |f x| ≤ M := sorry

theorem sum_weighted_abs_coeffs_le_one (n : ℕ) (hn : n > 0) (a : ℕ → ℝ) (f : ℝ → ℝ) (h_def : ∀ x : ℝ, f x = ∑ k in Finset.range n, a (k + 1) * Real.sin ((k + 1 : ℝ) * x)) (h_bound : ∀ x : ℝ, |f x| ≤ |Real.sin x|) : ∑ k in Finset.range n, (k + 1) * |a (k + 1)| ≤ 1 := sorry

theorem injectivity_of_f : ∀ (m n : ℕ), m ∈ S → n ∈ S → f m = f n → m = n := sorry

theorem max_sum_cyclic_products (n : ℕ) (hn : n ≥ 2) (x : ℕ → ℕ) (hx_range : Set.range x = Finset.Icc 1 n) (hx_inj : Function.Injective x) : 
    ∃ (T : ℕ), T = ∑ i : Finset.Icc 1 n, (x i.val) * (x ((i.val % n) + 1)) ∧ T ≤ ((2 * n^3 + 3 * n^2 - 11 * n + 18) / 6 : ℕ) := sorry

theorem rational_sum_identity (a : ℕ → ℚ) (h_a_even : ∀ n, Even n → a n = (n : ℚ) / 2) (h_a_odd : ∀ n, Odd n → a n = ((n - 1) : ℚ) / 2) (f : ℕ → ℚ) (h_f : ∀ n, f n = ∑ k in Finset.range (n + 1), a k) (x y : ℕ) (hx_pos : x > 0) (hy_pos : y > 0) (h_gt : x > y) : (x : ℚ) * (y : ℚ) = f (x + y) - f (x - y) := sorry

theorem exists_nonassociative_operation : ∃ (S : Type) (op : S → S → S), (∀ (x y : S), op x (op x y) = y) ∧ (∀ (x y : S), op (op y x) x = y) ∧ (∀ (a b : S), op a b = op b a) ∧ ∃ (a b c : S), ¬(op a (op b c) = op (op a b) c) := sorry

theorem complex_sum_sqrt_real_part_inequality (n : ℕ) (z : Fin n → ℂ) :
    let S := ∑ i : Fin n, (z i) ^ 2
    let w := Complex.csqrt S
    |Complex.re w| ≤ ∑ i : Fin n, |Complex.re (z i)| := sorry

theorem exists_interval_disjoint_from_sum_set (N : ℕ) (hN : N = 1994) (r : ℕ → ℝ) (hpos : ∀ n, r n > 0) (hlim : Filter.Tendsto r Filter.atTop (nhds 0)) (a b : ℝ) (hab : a < b) : ∃ c d : ℝ, a < c ∧ c < d ∧ d < b ∧ ((Set.Ioo c d) ∩ {x : ℝ | ∃ (indices : Finset ℕ) (hcard : indices.card = N) (hsorted : ∀ i ∈ indices, ∀ j ∈ indices, i < j → i.val < j.val), x = ∑ i in indices, r i} = ∅) := sorry

theorem exists_ab_from_xy (x y n : ℤ) (hn : 4 * n + 1 = x ^ 2 + y ^ 2) : ∃ a b : ℤ, n = ((a ^ 2 + a) / 2) + ((b ^ 2 + b) / 2) := sorry

theorem exists_y_with_sum_zero : ∃ (y : ℝ), f y + f'' y = 0 := sorry

theorem derivative_condition_implies_j_eq_eight : ∀ (j : ℕ) (hpos : j > 0), (∀ (p : ℤ[X]) (k : ℤ), ∃ (m : ℤ), Polynomial.eval (k : ℝ) ((Polynomial.derivative ^ j) p) = (2016 : ℝ) * (m : ℝ)) → j = 8 := sorry

theorem exists_max_n_with_a_eq_2020 : ∃ n : ℕ, a n = 2020 ∧ ∀ m : ℕ, n < m → a m ≠ 2020 := sorry

theorem exists_short_generating_sequence (c : ℝ) (hc : c > 0) (G : Type*) [Group G] [Fintype G] (hG : Nontrivial G) : 
    let n := Fintype.card G in
    n > 1 → ∃ (S : List G), List.length S ≤ ⌈c * Real.logb 2 (n : ℝ)⌉₊ ∧ ∀ (g : G), ∃ (T : List G), T.Sublist S ∧ T.prod = g := sorry

theorem k_n_eq_25 : k 1000000 = 25 := sorry

theorem exists_constant_for_sum_inequality : ∃ (k : ℝ), ∀ (a : ℕ → ℝ) (ha : ∀ n, 0 < a n), 
    (∑' n : ℕ, (n : ℝ) / (∑ i in Finset.range (n + 1), a i)) ≤ k * (∑' n : ℕ, 1 / a n) := sorry

theorem quadrilateral_side_equality (A B C D : ℝ × ℝ × ℝ) (h_non_coplanar : ¬ Coplanar ℝ {A, B, C, D}) (h_angle_ABC_eq_CDA : ∠ A B C = ∠ C D A) (h_angle_BCD_eq_DAB : ∠ B C D = ∠ D A B) : (dist A B = dist C D) ∧ (dist A D = dist B C) := sorry

theorem polynomial_roots_condition (b c : ℝ) (P : ℂ → ℂ) (hP_def : ∀ z, P z = z ^ 2 + (b : ℂ) * z + (c : ℂ)) (h_root1 : ∃ z1 : ℂ, P z1 = 0) (h_root2 : ∃ z2 : ℂ, P z2 = 0) (h_roots_bound : ∀ z : ℂ, P z = 0 → Complex.abs z < 1) : (b, c) ∈ {p : ℝ × ℝ | p.2 > -1 ∧ p.2 < 1 + p.1 ∧ p.2 < 1 - p.1} := sorry

theorem probability_intersection_lower_bound (n : ℕ) (a : ℝ) (h_a : a < 1/4) (A : ℕ → Set Ω) (h_prob : ∀ i, 1 ≤ i ∧ i ≤ n → ℙ (A i) ≥ 1 - a) (h_indep : ∀ i j, |(i : ℤ) - (j : ℤ)| > 1 → Indep (A i) (A j)) (u : ℕ → ℝ) (h_u0 : u 0 = 1) (h_u1 : u 1 = 1 - a) (h_u_rec : ∀ k ≥ 1, u (k + 1) = u k - a * u (k - 1)) (h_u_pos : ∀ k, u k > 0) : ℙ (⋂ i ∈ Finset.Icc 1 n, A i) ≥ u n := sorry

theorem area_of_region_R : volume (Set.mk (fun (p : ℝ × ℝ) => |p.1| - |p.2| ≤ 1 ∧ |p.2| ≤ 1) (by intro p; exact And.intro)) = 6 := sorry

theorem limit_ratio_equals_e : Filter.Tendsto (λ (x : ℝ) => (limUnder (nhds (0 : ℝ)) (λ (r : ℝ) => (((x + 1) ^ (r + 1) - x ^ (r + 1)) ^ (1 / r))) / x)) atTop (nhds (Real.exp 1)) := sorry

theorem existence_of_natural_numbers_implies_n_eq_one (n : ℕ) (hn_pos : n > 0) : 
    (∃ (a b c : ℕ), a > 0 ∧ b > 0 ∧ c > 0 ∧ 2 * (a ^ n) + 3 * (b ^ n) = 4 * (c ^ n)) → n = 1 := sorry

theorem tournament_schedule_exists (n : ℕ) (T : Set ℕ) (hT_card : Finset.card (Finset.filter (λ t => t ∈ T) Finset.univ) = 2 * n) (D : Set ℕ) (hD_card : Finset.card (Finset.filter (λ d => d ∈ D) Finset.univ) = 2 * n - 1) (f : ℕ → Set (ℕ × ℕ)) (hf_domain : ∀ d, d ∈ D → f d ⊆ T ×ˢ T) (hf_injective_pairs : ∀ d, d ∈ D → ∀ (p : ℕ × ℕ), p ∈ f d → p.1 ≠ p.2) (hf_team_coverage : ∀ d, d ∈ D → ∀ t ∈ T, ∃! (p : ℕ × ℕ), p ∈ f d ∧ (p.1 = t ∨ p.2 = t)) (g : ℕ × ℕ → ℕ) (hg_inverse : ∀ (x y : ℕ), x ∈ T → y ∈ T → x ≠ y → ∃! d, d ∈ D ∧ ((x, y) ∈ f d ∨ (y, x) ∈ f d)) : ∃ (h : ℕ → ℕ), (∀ d, d ∈ D → h d ∈ T) ∧ (∀ d, d ∈ D → ∃ (p : ℕ × ℕ), p ∈ f d ∧ p.1 = h d) ∧ (∀ d₁ d₂, d₁ ∈ D → d₂ ∈ D → d₁ ≠ d₂ → h d₁ ≠ h d₂) := sorry

theorem F_eq_n (n : ℕ) (hn : n > 0) : 
    let dist : ℝ → ℝ := λ x => |x - round x|
    let F : ℕ → ℝ := λ n => ∑ m in Finset.Icc 1 (6*n - 1), min (dist (m / (6*n : ℝ))) (dist (m / (3*n : ℝ)))
    in F n = n := sorry

theorem functional_equation_identity : ∀ (P : ℝ → ℝ), (∀ (x : ℝ), P (x ^ 2 + 1) = (P x) ^ 2 + 1) → P 0 = 0 → ∀ (x : ℝ), P x = x := sorry

