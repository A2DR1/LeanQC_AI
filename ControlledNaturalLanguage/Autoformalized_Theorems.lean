
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open BigOperators Real Nat Topology Rat


theorem exists_prime_gt (n : ℕ) : ∃ p, Nat.Prime p ∧ n < p := sorry

theorem log_property (x y z : ℝ) (w : ℝ) (hx : x > 1) (hy : y > 1) (hz : z > 1) (hw : w > 0) 
    (h1 : Real.logb x w = 24) (h2 : Real.logb y w = 40) (h3 : Real.logb (x * y * z) w = 12) : 
    Real.logb z w = 60 := sorry
