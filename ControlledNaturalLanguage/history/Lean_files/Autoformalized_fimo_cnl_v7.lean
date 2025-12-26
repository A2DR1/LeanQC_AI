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

theorem equivalence_of_Good_under_prime_divisibility_conditions (k : ℤ) (hk : k ≥ 2) (n n' : ℤ) (hn : n ≥ k) (hn' : n' ≥ k) 
    (h_prime_div_iff : ∀ (p : ℕ), Nat.Prime p → (p : ℤ) ≤ k → ((p : ℤ) ∣ n ↔ (p : ℤ) ∣ n')) 
    (S : Set ℕ := {p | Nat.Prime p ∧ (p : ℤ) ≤ k}) 
    (T : Set ℕ := {p ∈ S | (p : ℤ) ∣ n}) 
    (T' : Set ℕ := {p ∈ S | (p : ℤ) ∣ n'}) 
    (hT_eq_T' : T = T') 
    (f : ℕ → ℕ := λ m => if hm : k ≤ (m : ℤ) then 
        match (Finset.filter (λ m' => k ≤ (m' : ℤ) ∧ (m' : ℤ) < (m : ℤ) ∧ Nat.Coprime m' m) (Finset.Ico ⌊k⌋₊ m)).min' ?_ with
        | m' => m'
        end 
        else 0) 
    (Good : ℤ → Prop := λ x => x ≥ k ∧ ∃ (winning_strategy : ℤ → ℤ), True) : 
    Good n ↔ Good n' := sorry

theorem possible_values_of_P_at_zero : 
    {P : ℝ → ℝ | ∀ x y : ℝ, (|y ^ 2 - P x| ≤ 2 * |x|) ↔ (|x ^ 2 - P y| ≤ 2 * |y|)}.image (λ P => P 0) = Set.Iio (0 : ℝ) ∪ {1} := sorry

theorem polynomial_form (d : ℕ) (hd_odd : Odd d) (P : ℤ → ℤ) (hdeg : Polynomial.natDegree (Polynomial.ofFun P) = d) 
    (h : ∀ n : ℕ, ∃ (xs : Finset ℕ), xs.card = n ∧ ∀ i ∈ xs, ∀ j ∈ xs, 
        (1/2 : ℚ) < (P i : ℚ) / (P j : ℚ) ∧ (P i : ℚ) / (P j : ℚ) < (2 : ℚ) ∧ 
        ∃ (q : ℚ), (P i : ℚ) / (P j : ℚ) = q ^ d) : 
    ∃ (a r s : ℤ), a ≠ 0 ∧ r ≥ 1 ∧ Nat.Coprime (Int.natAbs r) (Int.natAbs s) ∧ 
    ∀ (x : ℤ), P x = a * ((r * x) + s) ^ d := sorry

theorem size_of_set : Finset.card (Finset.filter (λ n : ℕ => ∃ (a : ℕ → ℕ), (∑ i in Finset.Icc 1 n, (1 : ℚ) / ((2 : ℚ) ^ (a i))) = 1 ∧ (∑ i in Finset.Icc 1 n, (i : ℚ) * ((1 : ℚ) / ((3 : ℚ) ^ (a i)))) = 1) (Finset.range (Nat.succ n))) = ?_ := sorry

theorem exists_functions_satisfying_conditions : ∃ (f g : {x : ℝ | ∃ (a b : ℕ), x = (a : ℝ) - (1 / (b : ℝ))} → {x : ℝ | ∃ (a b : ℕ), x = (a : ℝ) - (1 / (b : ℝ))}), 
    (∀ (x y : {x : ℝ | ∃ (a b : ℕ), x = (a : ℝ) - (1 / (b : ℝ))}), (x : ℝ) < (y : ℝ) → (f x : ℝ) < (f y : ℝ)) ∧ 
    (∀ (x y : {x : ℝ | ∃ (a b : ℕ), x = (a : ℝ) - (1 / (b : ℝ))}), (x : ℝ) < (y : ℝ) → (g x : ℝ) < (g y : ℝ)) ∧ 
    (∀ (x : {x : ℝ | ∃ (a b : ℕ), x = (a : ℝ) - (1 / (b : ℝ))}), (f (g (g x)) : ℝ) < (g (f x) : ℝ)) := sorry

theorem exists_bound_on_sequence (N : ℕ) (hN : N = 2017) (a : ℕ → ℝ) (hdef : ∀ n, N < n → a n = - (⨆ (i j : ℕ) (h : i + j = n), a i + a j)) : ∃ M : ℝ, ∀ n, |a n| ≤ M := sorry

theorem inequality_problem (n : ℕ) (hn : n ≥ 3) (a : ℕ → ℝ) (ha_pos : ∀ k, 2 ≤ k ∧ k ≤ n → a k > 0) (ha_prod : ∏ k in Finset.Icc 2 n, a k = 1) : ∏ k in Finset.Icc 2 n, ((1 + a k) ^ k) > (n : ℝ) ^ n := sorry

theorem binomial_coefficient_condition_iff_prime (m : ℤ) (hm : m ≥ 2) : 
    (∀ n : ℤ, (m/3 : ℤ) ≤ n ∧ n ≤ (m/2 : ℤ) → ∃ q : ℤ, Nat.choose (Int.natAbs n) (Int.natAbs (m - 2 * n)) = (Int.natAbs n) * q) ↔ Nat.Prime (Int.natAbs m) := sorry

theorem functional_equation_solution : (∀ (x : ℝ), f x = x) ∨ (∀ (x : ℝ), f x = -x) := sorry

theorem infinite_primes_dividing_f (f : ℕ → ℕ) (h_nonconst : ¬∀ x y, f x = f y) (h_cond : ∀ a b, a ≠ b → ∃ k : ℤ, (f a : ℤ) - (f b : ℤ) = ((a : ℤ) - (b : ℤ)) * k) : 
    ∀ n, ∃ p, n < p ∧ Nat.Prime p ∧ ∃ c, p ∣ f c := sorry

theorem min_sum_floor_div_perm (n : ℕ) (hn : n > 0) : 
    let S := {σ : Equiv.Perm (Fin n) | True} in
    let f (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℕ := (σ i).val / (i.val + 1) in
    let F (σ : Equiv.Perm (Fin n)) : ℕ := ∑ i : Fin n, f σ i in
    (∃ σ : Equiv.Perm (Fin n), F σ = (Nat.log 2 n).toNat + 1) ∧ 
    (∀ σ : Equiv.Perm (Fin n), (Nat.log 2 n).toNat + 1 ≤ F σ) := sorry

theorem infinite_solutions : Set.Infinite {t : ℚ × ℚ × ℚ | let (x, y, z) := t in x ≠ 1 ∧ y ≠ 1 ∧ z ≠ 1 ∧ x * y * z = 1 ∧ (x^2 / ((x - 1)^2) + y^2 / ((y - 1)^2) + z^2 / ((z - 1)^2) = 1)} := sorry

theorem exists_linear_polynomial (m : ℤ) (hm : m ≠ 0) (P : ℝ → ℝ) (hP : ∀ x : ℝ, ((x ^ 3 - (m : ℝ) * x ^ 2 + 1) * P (x + 1)) + ((x ^ 3 + (m : ℝ) * x ^ 2 + 1) * P (x - 1)) = 2 * ((x ^ 3 - (m : ℝ) * x + 1) * P x)) : ∃ t : ℝ, ∀ x : ℝ, P x = t * x := sorry

theorem inequality_sum_ratio (n : ℕ) (hn : n ≥ 2) (a : ℕ → ℝ) (ha_pos : ∀ i, 1 ≤ i ∧ i ≤ n → 0 < a i) : 
    (∑ i in Finset.Icc 1 n, ∑ j in Finset.filter (λ j => j > i) (Finset.Icc 1 n), (a i * a j) / (a i + a j)) ≤ 
    ((n : ℝ) / (2 * ∑ k in Finset.Icc 1 n, a k)) * (∑ i in Finset.Icc 1 n, ∑ j in Finset.filter (λ j => j > i) (Finset.Icc 1 n), a i * a j) := sorry

theorem exists_distinct_polynomials_of_equal_multisets : ∃ (P Q : ℝ → ℝ) (hP : Polynomial ℝ) (hQ : Polynomial ℝ), 
    (hP : Polynomial) = Polynomial.ofFun P ∧ (hQ : Polynomial) = Polynomial.ofFun Q ∧ 
    P ≠ Q ∧ Polynomial.degree hP = (n : ℕ) + 1 ∧ Polynomial.degree hQ = (n : ℕ) + 1 ∧ 
    ∀ i ∈ I, Multiset.map P (Finset.val (Finset.Icc (a * i - b) (a * i))) = Multiset.map Q (Finset.val (Finset.Icc (a * i - b) (a * i)))) := sorry

theorem exists_linear_function : ∃ (b : ℤ) (a : ℤ), a > 0 ∧ ℧ a = 0 ∧ ∀ (x : ℤ), f x = a * x + b := sorry

theorem greedy_algorithm_bound : 
    let c := 2 in
    (∀ (n : ℕ) (hn : n > 0) (S : Finset ℝ) (hS : S.card = n) (greedy_seq : Fin n → ℝ) 
        (h_greedy_seq_range : Set.range greedy_seq = (S : Set ℝ)) 
        (h_greedy_construction : ∀ (i : Fin n), 
            let R_prev : Finset ℝ := S.filter (λ x => ∀ j : Fin i, greedy_seq j ≠ x) in
            greedy_seq i ∈ R_prev ∧ 
            ∀ y ∈ R_prev, 
                |∑ j : Fin i, greedy_seq j + greedy_seq i| ≤ |∑ j : Fin i, greedy_seq j + y|) in
        let price (seq : Fin n → ℝ) : ℝ := 
            Finset.sup' (Finset.attach (Finset.range n)) (by simp) 
                (λ i => |∑ j : Fin i.1, seq j|) in
        let D : ℝ := 
            Finset.inf' (S.permsOfSize n) (by 
                rcases hS with rfl
                exact Finset.one_lt_card.mp hn) 
                (λ σ => price σ) in
        price greedy_seq ≤ c * D) ∧
    (∀ (c' : ℝ), (∀ (n : ℕ) (hn : n > 0) (S : Finset ℝ) (hS : S.card = n) (greedy_seq : Fin n → ℝ) 
        (h_greedy_seq_range : Set.range greedy_seq = (S : Set ℝ)) 
        (h_greedy_construction : ∀ (i : Fin n), 
            let R_prev : Finset ℝ := S.filter (λ x => ∀ j : Fin i, greedy_seq j ≠ x) in
            greedy_seq i ∈ R_prev ∧ 
            ∀ y ∈ R_prev, 
                |∑ j : Fin i, greedy_seq j + greedy_seq i| ≤ |∑ j : Fin i, greedy_seq j + y|) in
        let price (seq : Fin n → ℝ) : ℝ := 
            Finset.sup' (Finset.attach (Finset.range n)) (by simp) 
                (λ i => |∑ j : Fin i.1, seq j|) in
        let D : ℝ := 
            Finset.inf' (S.permsOfSize n) (by 
                rcases hS with rfl
                exact Finset.one_lt_card.mp hn) 
                (λ σ => price σ) in
        price greedy_seq ≤ c' * D) → c ≤ c') := sorry

theorem exists_distinct_pos_ints_balanced_P : ∃ (a b : ℕ), 0 < a ∧ 0 < b ∧ a ≠ b ∧ ∀ n ∈ Finset.Icc 1 50, 
    let P := fun (x : ℕ) => (x + a) * (x + b) in
    (P n = 1) ∨ (∃ (k : ℕ), ∃ (primes : ℕ → ℕ), (∀ i : ℕ, Nat.Prime (primes i)) ∧ P n = ∏ i in Finset.range (2 * k), primes i) := sorry

theorem no_distinct_f_rare : ¬∃ (v w : ℤ) (hv : v ≠ w) (hvr : (Set.Finite {x | f x = v} ∧ Set.Nonempty {x | f x = v})) (hwr : (Set.Finite {x | f x = w} ∧ Set.Nonempty {x | f x = w})), True := sorry

theorem exists_partition_sum_le_one (V : ℚ) (hV : V = (99 : ℚ) + (1/2 : ℚ)) (C : Finset ℚ) (hC : ∀ c ∈ C, ∃ (n : ℕ) (hn : n > 0), c = (1 : ℚ) / (n : ℚ)) (hsum : ∑ c in C, c ≤ V) : 
    ∃ (partition : Finset (Finset ℚ)) (hpartition : partition.card ≤ 100), 
      (∀ S ∈ partition, S ⊆ C) ∧ 
      (∀ S ∈ partition, ∑ c in S, c ≤ 1) ∧ 
      (∀ c ∈ C, ∃! S ∈ partition, c ∈ S) := sorry

theorem problem : ∀ (f : ℤ → ℤ) (hf : ∀ x, 0 < x → 0 < f x), (∀ (m : ℤ) (hm : 0 < m) (n : ℤ) (hn : 0 < n), ∃ (k : ℤ), m * f m + n = ((m ^ 2 + f n) : ℤ) * k) → ∀ (n : ℤ) (hn : 0 < n), f n = n := sorry

theorem exists_periodic_after_N (a : ℕ → ℕ) (hpos : ∀ n, a n > 0) (hdiv : ∀ n m, ∃ k : ℤ, (a n + a (n + m)) = a (n + 2 * m) * k) : ∃ N d, ∀ n, N < n → a n = a (n + d) := sorry

theorem size_of_solutions : Finset.card (Finset.filter (λ (g : ℝ → ℝ) => ∀ (x : ℝ) (y : ℝ), g (g x * g y) + g (x + y) = g (x * y)) (Finset.univ : Finset (ℝ → ℝ))) = 3 := sorry

theorem sum_bound (n k : ℕ) (hn : n > 0) (hk : k > 0) (a : ℕ → ℝ) (ha_pos : ∀ i, 1 ≤ i ∧ i ≤ n → 1 ≤ a i) (ha_bound : ∀ i, 1 ≤ i ∧ i ≤ n → a i ≤ (2 : ℝ) ^ k) : 
    (∑ i in Finset.Icc 1 n, a i / Real.sqrt (∑ j in Finset.Icc 1 i, (a j) ^ 2)) ≤ 4 * Real.sqrt (k * n) := sorry

theorem problem (x : ℕ) (y : ℕ) (hx_pos : x > 0) (hy_pos : y > 0) 
    (h : ∀ (n : ℕ) (hn : n ≥ 1), ∃ (k : ℤ), (x : ℤ) ^ (2 ^ n) - 1 = ((2 ^ n : ℤ) * (y : ℤ) + 1) * k) : 
    x = 1 := sorry

theorem problem : ∀ (f : ℕ → ℕ), (∀ (m n p : ℕ), Nat.Prime p → (∃ (k1 : ℕ), f (m + n) = p * k1) ↔ (∃ (k2 : ℕ), f m + f n = p * k2)) → ∀ (n : ℕ), f n = n := sorry

theorem exists_int_m_for_k (k : ℕ) (hk : k > 0) (a : ℕ → ℤ) (c : ℤ) (h0 : a 0 = c) (h_rec : ∀ n : ℕ, n ≥ 1 → a n = (a (n - 1) + (n : ℤ) ^ k) / (n : ℤ)) (h_int : ∀ n : ℕ, n ≥ 1 → (a n : ℤ) = a n) : ∃ m : ℤ, (k : ℤ) - 2 = 3 * m := sorry

theorem exists_unique_pair : 
    ∃! (k n : ℕ), 0 < k ∧ 0 < n ∧ 0 < (7^k - 3^n) ∧ ∃ (m : ℤ), (k^4 + n^2 : ℤ) = ((7^k - 3^n) : ℤ) * m := by
  refine ⟨(2, 4), ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_, ?_⟩
    · have : (7 : ℤ)^2 - (3 : ℤ)^4 = 49 - 81 := by norm_num
      linarith
    · refine ⟨-1, ?_⟩
      norm_num
  · intro ⟨k, n⟩ ⟨hkpos, hnpos, hpos, hm⟩
    ext <;> dsimp
    sorry

theorem exists_polynomial_not_equal_for_permutation (n : ℕ) (hn : n > 0) (x : Fin (2 * n) → ℝ) (hx_strict : ∀ i : Fin (2 * n - 1), x ⟨i.val, by omega⟩ < x ⟨i.val + 1, by omega⟩) (P : ℝ[X]) (hP_deg : P.degree = n) (y : Fin (2 * n) → ℝ) (hy_def : ∀ i, y i = P.eval (x i)) (s : Equiv.Perm (Fin (2 * n))) (hs_monotone : ∀ i : Fin (2 * n - 1), y (s ⟨i.val, by omega⟩) ≤ y (s ⟨i.val + 1, by omega⟩)) : 
    ∃ (Q : ℝ[X]), Q.degree = n ∧ (∀ i, Q.eval (x i) = y (s i)) ∧ ¬(∀ (s' : Equiv.Perm (Fin (2 * n))), (∀ i : Fin (2 * n - 1), y (s' ⟨i.val, by omega⟩) ≤ y (s' ⟨i.val + 1, by omega⟩)) → Q = P) := sorry

theorem exists_int_power_eq (b n : ℤ) (hn : n > 1) (h : ∀ (k : ℤ), k > 1 → ∃ (a_k : ℤ) (m : ℤ), b - a_k ^ n = k * m) : ∃ (A : ℤ), b = A ^ n := sorry

theorem problem_2019 : 
    let n : ℕ := 2019 in
    let u : Fin n → ℝ := ?_ in
    (∑ i : Fin n, u i) = 0 → 
    (∑ i : Fin n, (u i) ^ 2) = 1 → 
    let a := Finset.inf' Finset.univ Finset.univ_nonempty u in
    let b := Finset.sup' Finset.univ Finset.univ_nonempty u in
    a * b ≤ (-1 : ℝ) / (n : ℝ) := sorry

theorem exists_constant_bound : ∃ C : ℝ, ∀ n : ℕ, n ≥ 1 → (φ (d n) : ℝ) / (d (φ n) : ℝ) ≤ C := sorry

theorem exists_partition_of_Z (hA_nonempty : Set.Nonempty A) (hB_nonempty : Set.Nonempty B) (hC_nonempty : Set.Nonempty C)
    (h_union : ∀ z : ℤ, z ∈ A ∨ z ∈ B ∨ z ∈ C)
    (h_disjoint_AB : ∀ z : ℤ, ¬(z ∈ A ∧ z ∈ B))
    (h_disjoint_AC : ∀ z : ℤ, ¬(z ∈ A ∧ z ∈ C))
    (h_disjoint_BC : ∀ z : ℤ, ¬(z ∈ B ∧ z ∈ C)) :
    ∃ (A B C : Set ℤ), Set.Nonempty A ∧ Set.Nonempty B ∧ Set.Nonempty C ∧
    (∀ z : ℤ, z ∈ A ∨ z ∈ B ∨ z ∈ C) ∧
    (∀ z : ℤ, ¬(z ∈ A ∧ z ∈ B)) ∧
    (∀ z : ℤ, ¬(z ∈ A ∧ z ∈ C)) ∧
    (∀ z : ℤ, ¬(z ∈ B ∧ z ∈ C)) ∧
    let A_plus_B : Set ℤ := {x | ∃ a ∈ A, ∃ b ∈ B, x = a + b}
    let B_plus_C : Set ℤ := {x | ∃ b ∈ B, ∃ c ∈ C, x = b + c}
    let C_plus_A : Set ℤ := {x | ∃ c ∈ C, ∃ a ∈ A, x = c + a}
    in (A_plus_B ∩ B_plus_C).Finite ∧ (A_plus_B ∩ C_plus_A).Finite ∧ (B_plus_C ∩ C_plus_A).Finite := sorry

theorem set_equality (a : ℕ) (ha_pos : a > 0) (ha_not_square : ¬∃ n : ℕ, n^2 = a) : 
    {k : ℕ | ∃ (x y : ℤ), (x : ℝ) > Real.sqrt a ∧ (k : ℤ) = (x^2 - a) / (x^2 - y^2)} = 
    {k : ℕ | ∃ (x y : ℤ), (0 ≤ x ∧ (x : ℝ) < Real.sqrt a) ∧ (k : ℤ) = (x^2 - a) / (x^2 - y^2)} := sorry

theorem largest_nonrepresentable_sum (n : ℤ) (hn : n ≥ 2) : 
    let A_n : Set ℤ := {x | ∃ k : ℤ, 0 ≤ k ∧ k < n ∧ x = 2^n - 2^k}
    in (∀ (S : Multiset ℤ) (hS : ∀ x ∈ S, x ∈ A_n), (S.sum : ℤ) ≠ ((n - 2) * 2^n + 1)) ∧
       (∀ (m : ℤ) (hm : 0 < m) (hm_lt : m < (n - 2) * 2^n + 1), 
          ∃ (S : Multiset ℤ) (hS : ∀ x ∈ S, x ∈ A_n), (S.sum : ℤ) = m) := sorry

theorem periodic_sequence : ∃ (T : ℕ) (hT : T ≥ 1), ∀ (n : ℤ⁺), a (n + T) = a n := sorry

theorem max_value_of_S : 
    ∀ (a b c d : ℝ), 
    0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → 
    a + b + c + d = 100 → 
    let S := (fun (a b c d : ℝ) => ((a / (b + 7)) ^ ((1 : ℝ)/3)) + ((b / (c + 7)) ^ ((1 : ℝ)/3)) + ((c / (d + 7)) ^ ((1 : ℝ)/3)) + ((d / (a + 7)) ^ ((1 : ℝ)/3))) a b c d
    in S ≤ ((8 : ℝ) / ((7 : ℝ) ^ ((1 : ℝ)/3))) ∧ 
       ∃ (a' b' c' d' : ℝ), 0 ≤ a' ∧ 0 ≤ b' ∧ 0 ≤ c' ∧ 0 ≤ d' ∧ a' + b' + c' + d' = 100 ∧ 
         (fun (a b c d : ℝ) => ((a / (b + 7)) ^ ((1 : ℝ)/3)) + ((b / (c + 7)) ^ ((1 : ℝ)/3)) + ((c / (d + 7)) ^ ((1 : ℝ)/3)) + ((d / (a + 7)) ^ ((1 : ℝ)/3))) a' b' c' d' = ((8 : ℝ) / ((7 : ℝ) ^ ((1 : ℝ)/3))) := sorry

theorem inequality_problem (a b c d : ℝ) (h_sum : a + b + c + d = 6) (h_sum_sq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 12) : 
    36 ≤ 4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ∧ 
    4 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) ≤ 48 := sorry

theorem set_cardinality_eq_four : Finset.card (Finset.filter (λ (pair : ℕ × ℕ) => pair.1 ^ 2 + 2 * (3 ^ pair.2) = pair.1 * ((2 ^ (pair.2 + 1)) - 1)) Finset.univ) = 4 := sorry

theorem set_equals_specific_pairs : Finset.filter (λ (pair : ℕ × ℕ) => pair.1 ^ 2 + 2 * (3 ^ pair.2) = pair.1 * ((2 ^ (pair.2 + 1)) - 1)) Finset.univ = {(6, 3), (9, 3), (9, 5), (54, 5)} := sorry

theorem exists_constants_for_S : ∃ (α β m M : ℝ), ∀ (x y : ℕ), (m < α * (x : ℝ) + β * (y : ℝ) ∧ α * (x : ℝ) + β * (y : ℝ) < M) ↔ (x, y) ∈ { p : ℕ × ℕ | ∃ (J : Finset ℕ) (_ : ∀ j ∈ J, 0 < j), x = ∑ j in J, (c j : ℤ) ∧ y = ∑ j in J, (c (j - 1) : ℤ) } := sorry

theorem exists_epsilon_d_c (n : ℕ) (hn1 : n ≥ 1) (hn_odd : Odd n) (f : ℤ → ℤ) 
    (h : ∀ (x y : ℤ), ∃ (k : ℤ), x ^ n - y ^ n = (f x - f y) * k) : 
    ∃ (ε : ℤ) (hε : ε ∈ ({1, -1} : Set ℤ)) (d : ℕ) (hd_pos : d > 0) (c : ℤ), 
    d ∣ n ∧ ∀ (x : ℤ), f x = ε * (x ^ d) + c := sorry

theorem triples_condition : 
    {p : ℕ | Nat.Prime p} × ℕ × ℕ = 
      ({(3, 2, 5), (3, 5, 2)} : Set (ℕ × ℕ × ℕ)) ∪ 
      {t : ℕ × ℕ × ℕ | ∃ (k n : ℕ), t = (2, n, 2^k - n) ∧ n > 0 ∧ n < 2^k} := sorry

theorem exists_rational_not_in_any_set (A B C : Set ℚ) (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty) (hC_nonempty : C.Nonempty)
    (h_union : ∀ x : ℚ, x ∈ A ∨ x ∈ B ∨ x ∈ C)
    (h_disjoint_AB : ∀ x : ℚ, ¬ (x ∈ A ∧ x ∈ B))
    (h_disjoint_AC : ∀ x : ℚ, ¬ (x ∈ A ∧ x ∈ C))
    (h_disjoint_BC : ∀ x : ℚ, ¬ (x ∈ B ∧ x ∈ C))
    (h_sum_AB : Set ℚ) (h_sum_BC : Set ℚ) (h_sum_CA : Set ℚ)
    (h_sum_AB_def : h_sum_AB = {s : ℚ | ∃ a ∈ A, ∃ b ∈ B, s = a + b})
    (h_sum_BC_def : h_sum_BC = {s : ℚ | ∃ b ∈ B, ∃ c ∈ C, s = b + c})
    (h_sum_CA_def : h_sum_CA = {s : ℚ | ∃ c ∈ C, ∃ a ∈ A, s = c + a})
    (h_disjoint_sum_AB_BC : ∀ s : ℚ, ¬ (s ∈ h_sum_AB ∧ s ∈ h_sum_BC))
    (h_disjoint_sum_AB_CA : ∀ s : ℚ, ¬ (s ∈ h_sum_AB ∧ s ∈ h_sum_CA))
    (h_disjoint_sum_BC_CA : ∀ s : ℚ, ¬ (s ∈ h_sum_BC ∧ s ∈ h_sum_CA)) :
    ∃ x : ℚ, ¬ (x ∈ A ∨ x ∈ B ∨ x ∈ C) := sorry

theorem no_positive_root (n k M : ℕ) (hM : M > 1) (a : ℕ → ℕ) (hsum : (∑ i in Finset.Icc 1 n, 1 / (a i : ℝ)) = (k : ℝ)) (hprod : ∏ i in Finset.Icc 1 n, a i = M) : ∀ (x : ℝ), x > 0 → ¬(M * ((x + 1) ^ k) = ∏ i in Finset.Icc 1 n, (x + (a i : ℝ))) := sorry

theorem max_sum_value : 
    let n : ℕ := 100
    let x : ℕ → ℝ := fun i => if h : 1 ≤ i ∧ i ≤ n then (x_i : ℝ) else 0
    let x_101 := x 1
    let x_102 := x 2
    (∀ i : ℕ, 1 ≤ i → i ≤ n → 0 ≤ x i) →
    (∀ i : ℕ, 1 ≤ i → i ≤ n → x i + x (i + 1) + x (i + 2) ≤ 1) →
    let S : ℝ := ∑ i in Finset.Icc 1 n, x i * x (i + 2)
    S ≤ 25/2 := sorry

theorem exists_sequence_with_midpoint_property (n : ℤ) (hn : n ≥ 2) : 
    ∃ (a : ℤ → ℤ) (hpos : ∀ i, 1 ≤ i ∧ i ≤ n → a i > 0) 
    (hnot_all_equal : ¬∀ i j, 1 ≤ i ∧ i ≤ n → 1 ≤ j ∧ j ≤ n → a i = a j),
    ∀ i j, 1 ≤ i ∧ i ≤ n → 1 ≤ j ∧ j ≤ n → ∃ k, 1 ≤ k ∧ k ≤ n ∧ (a i + a j) / 2 = a k := sorry

theorem exists_nonsquare_power_diff (a b : ℤ) (ha : a > 1) (hb : b > 1) (hne : a ≠ b) : 
    ∃ n : ℕ, ¬∃ k : ℤ, (a ^ n - 1) * (b ^ n - 1) = k ^ 2 := sorry

theorem exists_ordering_no_middle_multiple (n : ℕ) (hn : n ≥ 3) (S : Finset ℕ) (hSpos : ∀ x ∈ S, 0 < x) (hSsize : S.card = n) (hSsum : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c → a + b ≠ c) :
    ∃ (f : Fin n → ℕ) (h : Function.Bijective (f : Fin n → S)), ∀ i : ℕ, 2 ≤ i → i ≤ n - 1 → ¬∃ (k : ℤ), (f ⟨i - 1, by omega⟩ : ℕ) + (f ⟨i + 1, by omega⟩ : ℕ) = (f ⟨i, by omega⟩ : ℕ) * k := sorry

theorem theorem_name (n : ℕ) (hn : n > 0) (a_n : ℝ → ℝ) (h : ∀ x : ℝ, ((x^(2 * (2^n)) + 1) / 2) ^ ((2^n : ℝ)⁻¹) ≤ a_n ((x - 1)^2) + x) : a_n = λ _ => (2^n : ℝ) / 2 := sorry

theorem exists_factor_of_divisor_function_values (k : ℕ) (hk : 0 ≤ k) : 
    ∃ (t : ℤ), m = n * t := sorry

theorem exists_unique_n : ∃! n : ℕ, n ≥ 1 ∧ (z n : ℝ) < ((∑ i in Finset.range (n + 1), (z i : ℝ)) / (n : ℝ)) ∧ ((∑ i in Finset.range (n + 1), (z i : ℝ)) / (n : ℝ)) ≤ (z (n + 1) : ℝ) := sorry

theorem functional_set_size_two : 
    {g : ℝ → ℝ | ∀ (x : ℝ) (y : ℝ), g (x + g (x + y)) + g (x * y) = (x + g (x + y)) + y * g x} = {id, λ x => 2 - x} := sorry

theorem functional_equation_solutions : ∀ (f : ℤ → ℤ), (∀ (n : ℤ), n ^ 2 + 4 * f n = (f (f n)) ^ 2) ↔
  (∃ (f : ℤ → ℤ), (∀ (n : ℤ), f n = n + 1) ∧ (∀ (n : ℤ), n ^ 2 + 4 * f n = (f (f n)) ^ 2)) ∨
  (∃ (a : ℤ) (ha : a ≥ 1) (f : ℤ → ℤ), (∀ (n : ℤ), n > -a → f n = n + 1) ∧ (∀ (n : ℤ), n ≤ -a → f n = -n + 1) ∧ (∀ (n : ℤ), n ^ 2 + 4 * f n = (f (f n)) ^ 2)) ∨
  (∃ (f : ℤ → ℤ), (∀ (n : ℤ), n > 0 → f n = n + 1) ∧ (∀ (n : ℤ), n = 0 → f n = 0) ∧ (∀ (n : ℤ), n < 0 → f n = -n + 1) ∧ (∀ (n : ℤ), n ^ 2 + 4 * f n = (f (f n)) ^ 2)) := sorry

theorem functional_equation_implies_linear : ∀ (f : ℝ → ℝ), (∀ x, x > 0 → f x > 0) → (∀ x y, x > 0 → y > 0 → f (x + f y) = f (x + y) + f y) → ∀ x, x > 0 → f x = 2 * x := sorry

theorem exists_polynomial_form : ∃ (a : ℕ) (m : ℕ), ∀ (x : ℝ), f x = a * (x ^ m) := sorry

theorem excellent_set_size_eq_sum_divisors (ν : ℝ) (hν_pos : 0 < ν) (hν_irrational : Irrational ν) (m : ℕ) (hm_pos : 0 < m) :
    let good : ℕ × ℕ → Prop := λ ⟨a, b⟩ => (a : ℤ) * (⌈(b : ℝ) * ν⌉ : ℤ) - (b : ℤ) * (⌊(a : ℝ) * ν⌋ : ℤ) = (m : ℤ) in
    let excellent : ℕ × ℕ → Prop := λ ⟨a, b⟩ => good (a, b) ∧ ¬good (a - b, b) ∧ ¬good (a, b - a) in
    Finset.card (Finset.filter excellent (Finset.product Finset.univ Finset.univ : Finset (ℕ × ℕ))) = 
      ∑ d in Finset.filter (λ d => d ∣ m) (Finset.Icc 1 m), d := sorry

theorem least_k_with_empty_solution_set : 
    let n : ℕ := 2016
    let P : ℝ → ℝ := λ x => ∏ i in Finset.Icc 1 n, (x - (i : ℝ))
    let k : ℕ := ?_ in
    ∃ (k_min : ℕ), 
      (∀ (k' : ℕ), k' < k_min → ∀ (L R : ℝ → ℝ), 
        (∃ (S_L S_R : Finset ℕ), 
          S_L.card = k' ∧ S_R.card = k' ∧ 
          S_L ⊆ Finset.Icc 1 n ∧ S_R ⊆ Finset.Icc 1 n ∧
          L = λ x => ∏ i in (Finset.Icc 1 n : Finset ℕ) \ S_L, (x - (i : ℝ)) ∧
          R = λ x => ∏ i in (Finset.Icc 1 n : Finset ℕ) \ S_R, (x - (i : ℝ)) ∧
          (Finset.Icc 1 n : Finset ℕ) \ S_L ≠ ∅ ∧ (Finset.Icc 1 n : Finset ℕ) \ S_R ≠ ∅) → 
        Set.Nonempty {x : ℝ | L x = R x}) ∧
      (∃ (L_min R_min : ℝ → ℝ) (S_L_min S_R_min : Finset ℕ),
        S_L_min.card = k_min ∧ S_R_min.card = k_min ∧ 
        S_L_min ⊆ Finset.Icc 1 n ∧ S_R_min ⊆ Finset.Icc 1 n ∧
        L_min = λ x => ∏ i in (Finset.Icc 1 n : Finset ℕ) \ S_L_min, (x - (i : ℝ)) ∧
        R_min = λ x => ∏ i in (Finset.Icc 1 n : Finset ℕ) \ S_R_min, (x - (i : ℝ)) ∧
        (Finset.Icc 1 n : Finset ℕ) \ S_L_min ≠ ∅ ∧ (Finset.Icc 1 n : Finset ℕ) \ S_R_min ≠ ∅ ∧
        {x : ℝ | L_min x = R_min x} = ∅) := sorry

theorem constant_offset_function : ∀ (f : ℕ → ℕ), (∀ (m n : ℕ), ∃ (k : ℕ), (f m + n) * (m + f n) = k ^ 2) → ∃ (c : ℕ), ∀ (n : ℕ), f n = n + c := sorry

theorem size_of_fixed_points_le_degree (n : ℕ) (hn : n > 1) (P : ℤ → ℤ) (hPdeg : Polynomial.degree (Polynomial.map (Int.castRingHom ℤ) (Polynomial.ofFinsupp (Finsupp.ofSupportFinite (fun i => P i) (by
    have : Finite (Function.support (fun i : ℕ => P i)) := by
      apply Set.Finite.of_finite_image ?_ (Set.injOn_of_injective (fun x y h => by simpa using h) _)
      exact Set.finite_univ
    exact this))) = n) (k : ℕ) (hk : k > 0) : 
    let Q := Nat.iterate P k
    Finset.card (Finset.filter (fun x : ℤ => Q x = x) Finset.univ) ≤ n := sorry

theorem exists_infinitely_many_primes_with_sequences : ∀ n, ∃ p, n < p ∧ Nat.Prime p ∧
    ∃ (a b : ℕ → ℕ) (hpos_a0 : a 0 > 0) (hpos_b0 : b 0 > 0) (hcoprime_a0 : Nat.gcd (a 0) p = 1)
    (hcoprime_b0 : Nat.gcd (b 0) p = 1) (hlt : a 0 < b 0) (hodd : p % 2 = 1),
    (∀ n, a (n + 1) = a n + (Int.natAbs ((a n : ℤ) % (p : ℤ)))) ∧
    (∀ n, b (n + 1) = b n + (Int.natAbs ((b n : ℤ) % (p : ℤ)))) ∧
    (∀ n, n ≥ 1 → a n > b n) := sorry

theorem sum_a_le_n_sq (n : ℕ) (hn : n > 0) (a : ℕ → ℕ) (ha_pos : ∀ i, 1 ≤ i ∧ i ≤ n → a i > 0) (ha_periodic : ∀ i, a (n + i) = a i) (ha_mono : ∀ i, 1 ≤ i ∧ i ≤ n → a i ≤ a (i + 1)) (ha_bound1 : a n ≤ a 1 + n) (ha_bound2 : ∀ i, 1 ≤ i ∧ i ≤ n → a (a i) ≤ n + i - 1) : (∑ k in Finset.Icc 1 n, a k) ≤ n ^ 2 := sorry

theorem exists_integer_t (n : ℕ) (hn_odd : Odd n) (hn_pos : n > 0) (P : Set (ℝ × ℝ)) (hP_cyclic : Cyclic P) (S : ℝ) (hS_area : IsArea P S) (V : Set (ℤ × ℤ)) (hV_vertices : IsVertices P V) (m : ℕ) (hV_card : Fintype.card V = m) (v : ℕ → ℤ × ℤ) (hv_enum : ∀ i, i < m → v i ∈ V) (hv_surj : ∀ p ∈ V, ∃ i < m, v i = p) (x y : ℕ → ℤ) (hx : ∀ i, i < m → (v i).1 = x i) (hy : ∀ i, i < m → (v i).2 = y i) (L : ℕ → ℕ) (hL_def : ∀ i, i < m → L i = ((x ((i + 1) % m) - x i)^2 + (y ((i + 1) % m) - y i)^2)) (hk : ∀ i, i < m → ∃ (k_i : ℤ), (L i : ℤ) = n * k_i) : ∃ (t : ℤ), 2 * S = n * t := sorry

theorem sum_sqrt_abs_inequality (n : ℕ) (x : Fin n → ℝ) : ∀ (t : ℝ), 
    (∑ i : Fin n, ∑ j : Fin n, Real.sqrt (|x i - t|)) ≤ (∑ i : Fin n, ∑ j : Fin n, Real.sqrt (|x i + t|)) := sorry

theorem exists_k_of_cycle_condition (n : ℕ) (hn : n ≥ 3) (a : ℕ → ℝ) (h_periodic : a (n + 1) = a 1 ∧ a (n + 2) = a 2) (h_relation : ∀ i ∈ Finset.Icc 1 n, a i * a (i + 1) + 1 = a (i + 2)) : ∃ k : ℤ, (n : ℤ) = 3 * k := sorry

theorem inequality_problem (x y z : ℝ) (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) (hprod : x * y * z = 1) : 
    (x ^ 2 / ((x - 1) ^ 2)) + (y ^ 2 / ((y - 1) ^ 2)) + (z ^ 2 / ((z - 1) ^ 2)) ≥ 1 := sorry

theorem exists_function_with_bounded_gcd : ∃ (k : ℤ⁺) (f : ℤ⁺ → ℤ⁺), ∀ (m n : ℤ⁺), m ≠ n → Nat.gcd (f m + (n : ℕ)) (f n + (m : ℕ)) ≤ (k : ℕ) := sorry

theorem sum_product_condition (n : ℕ) (x : Fin n → ℝ) (h : ∀ i j : Fin n, i ≠ j → x i ≠ x j) : 
    (∑ i : Fin n, ∏ j : {j // j ≠ i}, ((1 - x i * x j) / (x i - x j))) = 
      if Even n then 0 else 1 := sorry

theorem size_of_L_set (a b : ℕ) (ha_pos : a > b) (hb_pos : b > 1) (h_gcd : Nat.gcd a b = 1) : 
    Finset.card (Finset.filter (λ c : ℤ => 
      let w : ℤ → ℕ := λ c => Nat.find (by
        have : ∃ (x y : ℤ), a * x + b * y = c := by
          have := Nat.gcd_eq_gcd_ab a b
          rw [h_gcd] at this
          refine ⟨(c : ℤ) * (Nat.gcdA a b : ℤ), (c : ℤ) * (Nat.gcdB a b : ℤ), ?_⟩
          simp [this]
        exact ⟨Finset.inf' (Finset.filter (λ (p : ℤ × ℤ) => a * p.1 + b * p.2 = c) Finset.univ) 
          (by simpa using this) (λ p => ‖p.1‖.natAbs + ‖p.2‖.natAbs), ?_⟩)
      w c ≥ w (c + a) ∧ w c ≥ w (c - a) ∧ w c ≥ w (c + b) ∧ w c ≥ w (c - b)) Finset.univ) = 
    if a % 2 = 1 ∧ b % 2 = 1 then b - 1 else 2 * (b - 1) := sorry

theorem exists_periodic_sequence : ∃ (N : ℕ) (t : ℕ), t > 0 ∧ ∀ (n : ℕ), n ≥ N → a (n + t) = a n := sorry

theorem factorial_multiple_inequality (a b : ℕ) (ha_pos : a > 0) (hb_pos : b > 0) (h_multiple : f a * f b ∣ f a + f b) : 3 * a ≥ 2 * b + 2 := sorry

theorem exists_polynomial_condition_implies_power_of_two_or_prime : 
    ∀ (n : ℕ) (hn : n > 0), 
    (∃ (P : ℤ → ℤ) (hP : ∀ x, ∃ (coeffs : List ℤ), ∀ (i : ℕ), 
        (Polynomial.eval x (Polynomial.ofFinsupp (Finsupp.ofList coeffs)) : ℤ) = P x) ∧ 
        (∀ (m : ℕ) (hm : m ≥ 1), 
            Fintype.card {r : ℤ // ∃ (i : ℕ) (hi : i ∈ Finset.Icc 1 n), 
                (Nat.iterate P m) (i : ℤ) ≡ r [ZMOD n]} = 
            Nat.ceil ((n : ℝ) / ((2 : ℝ) ^ m)))) → 
    (∃ (k : ℕ), n = 2 ^ k) ∨ Nat.Prime n := sorry

theorem size_of_set : Finset.card (Finset.filter (λ k : ℕ => ∃ f : ℕ → ℕ, (∀ m n : ℕ, f (m + n) ≥ f m + f (f n) - 1) ∧ f 2007 = k) Finset.univ) = 2008 := sorry

theorem prime_conclusion (a b : ℕ) (ha : a > 0) (hb : b > 0) 
    (P : ∀ n : ℕ, n > 0 → a * n ≥ b → ∃ k : ℤ, (Nat.choose (a * n) b : ℤ) - 1 = (a * n + 1 : ℤ) * k)
    (h_exists : ∃ m : ℕ, m > 0 ∧ a * m ≥ b + 2 ∧ ∀ t : ℤ, (Nat.choose (a * m) (b + 2) : ℤ) - 1 ≠ (a * m + 1 : ℤ) * t) : 
    Nat.Prime (b + 1) := sorry

theorem exists_non_square_digit_sum (a : ℕ → ℕ) (h_nonzero : ∀ i, a i ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9} : Set ℕ)) (N : ℕ) (hN_pos : N > 0) : 
    (∀ k > N, ∃ m : ℤ, (∑ i in Finset.range k, a (i + 1) * (10 : ℤ) ^ i) = m ^ 2) → 
    ∃ k > N, ¬∃ m : ℤ, (∑ i in Finset.range k, a (i + 1) * (10 : ℤ) ^ i) = m ^ 2 := sorry

theorem f_nonneg_for_3p (t : ℤ → ℤ) (f : ℤ → ℤ) (h_t_def : ∀ (m : ℤ), t m ∈ ({1, 2, 3} : Set ℤ) ∧ ∃ (k : ℤ), m + t m = 3 * k) (h_f_neg_one : f (-1) = 0) (h_f_zero : f 0 = 1) (h_f_one : f 1 = -1) (h_f_rec : ∀ (n : ℤ) (m : ℤ), n ≥ 0 → m ≥ 0 → (2 : ℤ) ^ n > m → f ((2 : ℤ) ^ n + m) = f ((2 : ℤ) ^ n - t m) - f m) (p : ℤ) (hp : p ≥ 0) : f (3 * p) ≥ 0 := sorry

theorem exists_infinite_subsets_of_S : 
    ∃ (A B : Set ℕ), A ⊆ S ∧ B ⊆ S ∧ Set.Infinite A ∧ Set.Infinite B ∧ 
    (∀ x ∈ A, ∃ (k : ℕ) (i : Fin k → ℕ), 2 ≤ k ∧ Function.Injective i ∧ x = ∑ j : Fin k, a (i j)) ∧ 
    (∀ y ∈ B, ¬∃ (m : ℕ) (j : Fin m → ℕ), 2 ≤ m ∧ Function.Injective j ∧ y = ∑ l : Fin m, a (j l)) := sorry

theorem exists_infinite_set_odd_a (n : ℤ) (hn : n > 1) : ∃ (S : Set ℕ), Set.Infinite S ∧ ∀ k ∈ S, Odd (Int.floor ((n : ℝ) ^ k / (k : ℝ))) := sorry

theorem exists_triple_in_subset (n : ℤ) : 
    let N := (5 : ℤ) ^ n in
    let A : Finset ℤ := Finset.Icc 0 N in
    (h : A.card = 4 * n + 2) → 
    ∃ a b c ∈ A, a < b ∧ b < c ∧ c + 2 * a > 3 * b := sorry

theorem problem (q : ℝ) (S : Finset ℝ) (hS : S.card = 10) (hS_distinct : (S : Set ℝ).InjOn id) (L₁ : Set ℝ := {z | ∃ a ∈ S, ∃ b ∈ S, z = a - b}) (L₂ : Set ℝ := {z | ∃ x ∈ L₁, ∃ y ∈ L₁, z = q * x * y}) (L₃ : Set ℝ := {z | ∃ x₁ ∈ L₁, ∃ x₂ ∈ L₁, ∃ x₃ ∈ L₁, ∃ x₄ ∈ L₁, z = x₁ ^ 2 + x₂ ^ 2 - x₃ ^ 2 - x₄ ^ 2}) (h : ∀ z ∈ L₂, z ∈ L₃) : q = -2 ∨ q = 0 ∨ q = 2 := sorry

theorem finite_solutions : Set.Finite {x : ℕ × ℕ × ℕ × ℕ | let (a, b, c, n) := x in a > 0 ∧ b > 0 ∧ c > 0 ∧ n > 0 ∧ (Nat.factorial n = a ^ (n - 1) + b ^ (n - 1) + c ^ (n - 1))} := sorry

theorem finite_subsets_sum_reciprocal_condition (S : Set ℕ) (hS : ∀ x ∈ S, 0 < x) :
    (∃ (F G : Finset ℕ) (hF : F ⊆ S) (hG : G ⊆ S), F ≠ G ∧ ∑ x in F, (1 : ℚ) / (x : ℚ) = ∑ x in G, (1 : ℚ) / (x : ℚ)) ∨
    (∃ (r : ℚ), 0 < r ∧ r < 1 ∧ ∀ (F : Finset ℕ) (hF : F ⊆ S), ∑ x in F, (1 : ℚ) / (x : ℚ) ≠ r) := sorry

theorem exists_n_and_m_i_iff_a_in_set : {a : ℕ | ∃ (n : ℕ), ∀ (i : ℕ), i < a → ∃ (m_i : ℤ), (t (n + a + i) - t (n + i) : ℤ) = 4 * m_i} = ({1, 3, 5} : Set ℕ) := sorry

theorem friendly_integer_set_size : 
    let A : Set ℕ := {x | 1 ≤ x ∧ x ≤ 2012} in
    let friendly (a : ℕ) : Prop := ∃ (m : ℕ) (n : ℕ), m > 0 ∧ n > 0 ∧ ((m ^ 2 + n) * (n ^ 2 + m) = a * ((m - n) ^ 3)) in
    (A.filter friendly).card ≥ 500 := sorry

theorem rational_y_of_rational_x : 
    ∀ (x : ℝ) (hx_pos : 0 < x) (hx_lt_one : x < 1) (hx_rat : ∃ (p q : ℤ), (q : ℝ) ≠ 0 ∧ x = (p : ℝ) / q),
    let S : Set ℕ := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} in
    let digit : ℕ → ℕ := λ n => Nat.digit 10 n (by exact ⟨hx_pos, hx_lt_one⟩) in
    let y : ℝ → ℝ := λ t => Real.ofDigits 10 (λ n => digit (2 ^ n)) in
    ∃ (p q : ℤ), (q : ℝ) ≠ 0 ∧ y x = (p : ℝ) / q := sorry

theorem exists_counterexample : ∃ (x : ℕ), ¬(f (g (g x)) < g (f x)) := sorry

theorem unbounded_k_n : ∀ M : ℕ, ∃ n : ℕ, k_n n > M := sorry

theorem smallest_k_for_planes_covering_S (n : ℤ) (hn : n > 1) : 
    let S : Set (ℤ × ℤ × ℤ) := {(x, y, z) | x ∈ Set.Icc (0 : ℤ) n ∧ y ∈ Set.Icc (0 : ℤ) n ∧ z ∈ Set.Icc (0 : ℤ) n ∧ (x + y + z) > 0}
    in let card_S : ℕ := ((n + 1)^3 - 1).toNat in
    ∃ (k : ℕ) (hk_pos : k > 0), 
      (∀ (planes : Finset (Set (ℤ × ℤ × ℤ))) (hcard : planes.card = k), 
        (∀ P ∈ planes, ∃ (a b c d : ℤ) (h : (a, b, c) ≠ (0, 0, 0)), 
          P = {(x, y, z) : ℤ × ℤ × ℤ | a * x + b * y + c * z + d = 0} ∧ d ≠ 0) → 
        (∀ p ∈ S, ∃ P ∈ planes, p ∈ P)) → 
      (∀ (k' : ℕ) (hk'_pos : k' > 0) (h : k' < k), 
        ¬∃ (planes : Finset (Set (ℤ × ℤ × ℤ))) (hcard : planes.card = k'), 
          (∀ P ∈ planes, ∃ (a b c d : ℤ) (h : (a, b, c) ≠ (0, 0, 0)), 
            P = {(x, y, z) : ℤ × ℤ × ℤ | a * x + b * y + c * z + d = 0} ∧ d ≠ 0) ∧ 
          (∀ p ∈ S, ∃ P ∈ planes, p ∈ P))) ∧ 
      k = 3 * n.toNat := sorry

theorem inequality_problem (n : ℕ) (hn : n > 0) (x : ℝ) (hx : x > 0) (y : ℝ) (hy : y > 0) (h : x ^ n + y ^ n = 1) : 
    let S_x : ℕ → ℝ := λ k => (1 + x ^ (2 * k)) / (1 + x ^ (4 * k))
    let S_y : ℕ → ℝ := λ k => (1 + y ^ (2 * k)) / (1 + y ^ (4 * k))
    in (∑ k in Finset.Icc 1 n, S_x k) * (∑ k in Finset.Icc 1 n, S_y k) < 1 / ((1 - x) * (1 - y)) := sorry

theorem inequality_problem (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a * b ≥ 1) (hbc : b * c ≥ 1) (hca : c * a ≥ 1) : 
    ((a ^ 2 + 1) * (b ^ 2 + 1) * (c ^ 2 + 1)) ^ ((1 : ℝ) / 3) ≤ ((a + b + c) / 3) ^ 2 + 1 := sorry

theorem infinite_primes_with_non_related_pair : ∀ (n : ℕ), ∃ (p : ℕ), n < p ∧ Nat.Prime p ∧ ∃ (a b : ℕ), a ∈ Finset.Icc 1 p ∧ b ∈ Finset.Icc 1 p ∧ a ≠ b ∧ ¬ (TransGen (λ (x y : ℕ) => ∃ (k : ℤ), ((x : ℤ)^2 - (y : ℤ) + 1) * ((y : ℤ)^2 - (x : ℤ) + 1) = (p : ℤ) * k) a b) := sorry

theorem a_value : a = 4/9 := sorry

theorem functional_equation_solution : ∀ (f : ℝ → ℝ) (hpos : ∀ x, x > 0 → f x > 0), (∀ (p q r s : ℝ) (hp : p > 0) (hq : q > 0) (hr : r > 0) (hs : s > 0), p * q = r * s → ((f p)^2 + (f q)^2) / (f (r^2) + f (s^2)) = (p^2 + q^2) / (r^2 + s^2)) → (∀ x, x > 0 → f x = x) ∨ (∀ x, x > 0 → f x = 1 / x) := sorry

theorem theorem_statement (a : ℕ → ℕ) (hpos : ∀ i, a i > 0) (hrec : ∀ i, i ≥ 1 → ∃ (k : ℤ), (Nat.gcd (a i) (a (i + 1)) : ℤ) = (a (i - 1) : ℤ) + k ∧ k > 0) : ∀ n, a n ≥ 2 ^ n := sorry

theorem exists_infinite_primes_with_sequences : 
    ∀ (p : ℕ) (hp : Nat.Prime p) (hp_odd : Odd p), 
    ∃ (a b : ℕ → ℕ) (ha0_pos : 0 < a 0) (ha0_coprime : Nat.Coprime (a 0) p) 
    (hb0_pos : 0 < b 0) (hb0_coprime : Nat.Coprime (b 0) p),
    (∀ n, a (n + 1) = a n + (a n : ℤ).mod p) ∧ 
    (∀ n, b (n + 1) = b n + (b n : ℤ).mod p) ∧ 
    Set.Infinite {n : ℕ | a n > b n} ∧ 
    Set.Infinite {n : ℕ | b n > a n} := sorry

theorem exists_positive_integers_product (k n : ℕ) (hk : k > 0) (hn : n > 0) : 
    ∃ (m : ℕ → ℕ), (∀ i, m i > 0) ∧ (1 + ((2 ^ k - 1) : ℚ) / n) = ∏ i in Finset.range k, (1 + (1 : ℚ) / (m i : ℚ)) := sorry

theorem inequality_problem (a b c d : ℝ) (ha : a ≥ b) (hb : b ≥ c) (hc : c ≥ d) (hd : d > 0) (hsum : a + b + c + d = 1) : (a + 2 * b + 3 * c + 4 * d) * ((a ^ a) * (b ^ b) * (c ^ c) * (d ^ d)) < 1 := sorry

theorem theorem_statement : ∃ n : ℕ, n = 2017 ∧ (a n ≥ (2017 : ℤ) ∨ a (n + 1) ≥ (2017 : ℤ)) := sorry

theorem balanced_implies_equal (a b : ℕ) (ha : a > 0) (hb : b > 0) : 
    (∀ n : ℕ, n > 0 → Balanced ((n + a) * (n + b))) → a = b := sorry

theorem sum_bound (n : ℕ) (hn : n > 0) : 
    let m := 2 * n in
    ∀ (x : Fin m → ℝ) (hx : ∀ i, -1 ≤ x i ∧ x i ≤ 1),
    let S := ∑ r : Fin m, ∑ s in Finset.filter (λ s => r.val < s.val) Finset.univ, ((s.val - r.val - n : ℝ) * (x r * x s)) in
    S ≤ n * (n - 1) := sorry

theorem sum_bound : 
    let n : ℕ := 100
    let a : ℕ → ℝ := a
    in (∀ i : ℕ, i ∈ Finset.Icc 1 n → a i ≥ 0) → 
       (∑ i in Finset.Icc 1 n, (a i) ^ 2 = 1) → 
       (∑ i in Finset.Icc 1 n, (a i) ^ 2 * a ((i % n) + 1)) < 12/25 := sorry

