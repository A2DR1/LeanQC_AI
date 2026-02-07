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

theorem expected_value_of_det_A_minus_A_transpose {n : ℕ} :
    (∑ A in (Finset.Icc 1 (2 * n)).powerset, (if A.card = 2 * n then (1 / 2 ^ (2 * n)) else 0) *
      (A \ (A.transpose : Set (Fin (2 * n) × Fin (2 * n)))) =
    ((Nat.factorial (2 * n)) / (4 ^ n * Nat.factorial n)) := by sorry

theorem number_theory_987 {p : ℕ} (hp : Nat.Prime p) (hp1 : 3 < p)
(I : ℕ → ℕ) (hI : ∀ k ∈ Finset.Icc 1 (p - 1), k * I k ≡ 1 [MOD p]) :
{(k : ℕ) | k ∈ Finset.Icc 1 (p - 2) ∧ I (k + 1) < I k}.ncard > (p / 4 : ℚ) - 1 :=
sorry

theorem sum_of_series (p : ℕ → ℝ)
(hpos : ∀ n, 0 < p n)
(hconv : ∃ L, Tendsto (λ n => ∑ i in range n, 1 / p i) atTop (𝓝 L))
: ∃ L, Tendsto (λ n => ∑ i in range n, (i + 1)^2 * p i / (∑ j in range (i + 1), p j)^2) atTop (𝓝 L) :=
sorry

theorem formalization_487924
  {n : ℕ}
  (hn : 0 < n)
  (A B M : Matrix (Fin n) (Fin n) ℝ)
  (hAB : A * M = M * B)
  (hAB' : A.charpoly = B.charpoly) :
  ∀ X : Matrix (Fin n) (Fin n) ℝ,
    (A - M * X).det = (B - X * M).det :=
sorry

theorem formalization_98768 :
  {v ∈ P | ∃ s t : Finset (ℤ × ℤ),
    s ⊆ P \ {v} ∧ t ⊆ P \ {v} ∧
    s.card = t.card ∧
    ∑ i in s, i.1 = ∑ i in t, i.1} =
  {v | 0 ≤ v.2 ∧ v.2 ≤ 100 ∧ Even v.2} := by sorry

