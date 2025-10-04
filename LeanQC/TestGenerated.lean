import Mathlib
import Aesop
set_option maxHeartbeats 0
-- set_option pp.numericTypes true
set_option pp.coercions true
set_option pp.letVarTypes true
set_option pp.structureInstanceTypes true
set_option pp.instanceTypes true
-- set_option pp.mvars.withType true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
open scoped BigOperators
open Real Nat Topology Rat Filter


/- Given probabilities p_0,p_1,p_2,p_3 with p_i \ge 0 and p_0+p_1+p_2+p_3=1, let p be the smallest positive real root of
p_0 + p_1 x + p_2 x^2 + p_3 x^3 = x.
Prove that if \mathbb E[X] = p_1 + 2p_2 + 3p_3 \le 1 then p=1, and if \mathbb E[X] > 1 then p<1. -/
theorem gaokaoformal_g_51
(p₀ p₁ p₂ p₃ p : ℝ)
(hprob : 0 ≤ p₀ ∧ 0 ≤ p₁ ∧ 0 ≤ p₂ ∧ 0 ≤ p₃ ∧ p₀ + p₁ + p₂ + p₃ = 1)
(hminroot :
(0 < p ∧ p₀ + p₁ * p + p₂ * p^2 + p₃ * p^3 = p) ∧
(∀ y : ℝ, 0 < y ∧ p₀ + p₁ * y + p₂ * y^2 + p₃ * y^3 = y → p ≤ y)) :
((p₁ + 2 * p₂ + 3 * p₃ ≤ 1) → p = 1) ∧
((1 < p₁ + 2 * p₂ + 3 * p₃) → p < 1) := by sorry

/-Given the function f(x)=(x - 1)e^{x}-ax^{2}+b.
Choose one of the following two conditions and prove that f(x) has exactly one zero:
① \frac{1}{2}< a\leq\frac{e^{2}}{2}，b > 2a；
② 0 < a<\frac{1}{2}，b\leq2a．-/
theorem gaokaoformal_g_91
(a b : ℝ)
(f : ℝ → ℝ)
(hf : ∀ x : ℝ, f x = (x - 1) * Real.exp x - a * x^2 + b) :
((1/2 < a ∧ a ≤ Real.exp 2 / 2 ∧ b > 2 * a) ∨ (0 < a ∧ a < 1/2 ∧ b ≤ 2 * a)) →
∃! x : ℝ, f x = 0 := by sorry

/-Let a, b be real numbers, and a > 1. The function f(x) = a^{x} - bx + e^{x} (where x \in \mathbf{R}) when a = e, prove that for any b > e^{4}, the function f(x) has two distinct zeros x_{1}, x_{2} satisfying x_{2} > \frac{b \ln b}{2e^{2}}x_{1} + \frac{e^{2}}{b}. (Note: e = 2.71828\cdots is the base of the natural logarithm.)-/
theorem gaokaoformal_g_92
(a b : ℝ)
(ha : a > 1)
(hae : a = Real.exp 1)
(f : ℝ → ℝ)
(hf : ∀ x : ℝ, f x = a^x - b * x + Real.exp x)
(hb : b > Real.exp 4) :
∃ x₁ x₂ : ℝ,
x₁ ≠ x₂ ∧
f x₁ = 0 ∧
f x₂ = 0 ∧
x₂ > (b * Real.log b) / (2 * Real.exp 2) * x₁ + (Real.exp 2) / b := by sorry

/-Given an infinite sequence \{ a_{n}\} with no zero term, two properties are provided:
① For any two terms a_{i}, a_{j} (i > j) in \{ a_{n}\},
there exists a term a_{m} in \{ a_{n}\} such that \frac{a_{i}^{2}}{a_{j}} = a_{m};
② For any term a_{n} (n \geq 3) in \{ a_{n}\},
there exist two terms a_{k}, a_{l} (k > l) in \{ a_{n}\} such that a_{n} = \frac{a_{k}^{2}}{a_{l}}.
If \{ a_{n}\} is a strictly increasing sequence and satisfies both property ① and property ②,
prove that \{ a_{n}\} is a geometric sequence.-/
theorem gaokaoformal_g_93
(a : ℕ → ℝ)
(hnz : ∀ n : ℕ, 1 ≤ n → a n ≠ 0)
(hinc : ∀ n : ℕ, 1 ≤ n → a (n + 1) > a n)
(hP₁ : ∀ i j : ℕ, (1 ≤ j ∧ j < i) → ∃ m : ℕ, a m = (a i)^2 / (a j))
(hP₂ : ∀ n : ℕ, 3 ≤ n → ∃ k l : ℕ, (1 ≤ l ∧ l < k) ∧ a n = (a k)^2 / (a l)) :
∃ r : ℝ, r ≠ 0 ∧ ∀ n : ℕ, 1 ≤ n → a (n + 1) = r * a n := by sorry

/-Given functions y = f(x), y = g(x), and h(x) = kx + b (k, b \in \mathbf{R}) defined on an interval D, such that f(x) \geq h(x) \geq g(x) holds for all x in D. If f(x) = x^{4} - 2x^{2}, g(x) = 4x^{2} - 8, h(x) = 4(t^{2} - t)x - 3t^{4} + 2t^{2} (0 < |t| \leq \sqrt{2}), and D = [m, n] \subseteq [-\sqrt{2}, \sqrt{2}], prove that n - m \leq \sqrt{7}.-/
theorem gaokaoformal_g_94
(t m n : ℝ)
(ht : 0 < |t| ∧ |t| ≤ Real.sqrt 2)
(f g h : ℝ → ℝ)
(hf : ∀ x : ℝ, f x = x^4 - 2 * x^2)
(hg : ∀ x : ℝ, g x = 4 * x^2 - 8)
(hh : ∀ x : ℝ, h x = 4 * (t^2 - t) * x - 3 * t^4 + 2 * t^2)
(hmn : m ≤ n)
(hbounds : - Real.sqrt 2 ≤ m ∧ n ≤ Real.sqrt 2)
(horder : ∀ x : ℝ, x ∈ Set.Icc m n → f x ≥ h x ∧ h x ≥ g x) :
n - m ≤ Real.sqrt 7 := by sorry

/-Given A and B as the left and right vertices of the ellipse E:\frac{x^{2}}{a^{2}}+y^{2}=1 (a > 1), respectively,
and G as the top vertex of E, with \overrightarrow{AG}\cdot\overrightarrow{GB}=8.
Let P be a moving point on the line x = 6, PA intersects E at another point C, and PB intersects E at another point D.
Prove that the line CD passes through a fixed point.-/
theorem gaokaoformal_g_95
(a : ℝ)
(ha : a > 1)
(E : Set (ℝ × ℝ))
(hE : E = {p : ℝ × ℝ | p.1^2 / a^2 + p.2^2 = 1})
(A B G : ℝ × ℝ)
(hA : A = (-a, 0))
(hB : B = (a, 0))
(hG : G = (0, 1))
(hAGGB : (G.1 - A.1) * (B.1 - G.1) + (G.2 - A.2) * (B.2 - G.2) = 8) :
∃ (X : ℝ × ℝ),
∀ (P C D : ℝ × ℝ),
(P.1 = 6) →
-- – C is the second intersection of line PA with the ellipse
((C ∈ E) ∧ C ≠ A ∧ (C.2 - P.2) * (A.1 - P.1) = (C.1 - P.1) * (A.2 - P.2)) →
-- – D is the second intersection of line PB with the ellipse
((D ∈ E) ∧ D ≠ B ∧ (D.2 - P.2) * (B.1 - P.1) = (D.1 - P.1) * (B.2 - P.2)) →
-- – Collinearity of C, D, X:
(X.2 - C.2) * (X.1 - D.1) = (X.1 - C.1) * (X.2 - D.2) := by sorry


/-Given the function f(x)=\sin^{2}x\sin2x, prove that \vert f(x)\vert\leq\frac{3\sqrt{3}}{8}.-/
theorem gaokaoformal_g_96 :
∀ x : ℝ, |(Real.sin x)^2 * Real.sin (2 * x)| ≤ (3 * Real.sqrt 3) / 8 := by sorry

/-For n\in\mathbf{N}^{*} and x∈ ℝ, prove that \sin^{2}x\sin^{2}2x\sin^{2}4x\cdots\sin^{2}2^{n}x\leq\frac{3^{n}}{4^{n}}.-/
theorem gaokaoformal_g_97
(n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
∏ k in Finset.range (n+1), (Real.sin ((2 : ℝ)^k * x))^2 ≤ (3 / 4 : ℝ) ^ n := by sorry
