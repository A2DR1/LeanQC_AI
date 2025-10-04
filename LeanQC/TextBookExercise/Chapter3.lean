import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic


-- 3.1.10 Exercises

-- 1
example : Odd (-9 : ℤ) := by
  dsimp [Odd]
  use -5
  norm_num

-- 2
example : Even (26 : ℤ) := by
  dsimp [Even]
  use 13
  norm_num

-- 3
example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  dsimp [Odd, Even]
  obtain ⟨k, hk⟩ := hm
  obtain ⟨l, hl⟩ := hn
  use k + l
  calc
    n + m = l + l + m := by rw[hl]
    _ = l + l + (2 * k + 1) := by rw[hk]
    _ = (l + k) + (l + k) + 1 := by ring
    _ = 2 * (l + k) + 1 := by ring
    _ = 2 * (k + l) + 1 := by ring

-- 4
example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  sorry
