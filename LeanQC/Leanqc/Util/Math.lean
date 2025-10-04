import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Fin
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Matrix.Kronecker
-- import LeanCopilot
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

open Matrix
open Kronecker

theorem conjTranspose_kronecker (A : Matrix m n ℂ) (B : Matrix l o ℂ) :
    (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
  ext
  simp

abbrev flatten_kronecker (M: Matrix (Fin d1 × Fin d2) (Fin 1 × Fin 1) ℂ): Matrix (Fin (d1 * d2)) (Fin 1) ℂ:= reindex finProdFinEquiv finProdFinEquiv M

abbrev flatten_kronecker_dual (M: Matrix (Fin 1 × Fin 1) (Fin d1 × Fin d2) ℂ): Matrix (Fin 1) (Fin (d1 * d2)) ℂ:= reindex finProdFinEquiv finProdFinEquiv M

-- TODO: Use https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fin/Basic.html#Fin.castIso
def fin22Fin4Equiv: Fin (2 * 2) ≃ Fin 4
    where
  toFun x := match x with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => 2
    | ⟨3, _⟩ => 3
  invFun x:= match x with
    | 0 => ⟨0, zero_lt_four⟩
    | 1 => ⟨1, by norm_num⟩
    | 2 => ⟨2, by norm_num⟩
    | 3 => ⟨3, by norm_num⟩
  left_inv := fun x => Fin.eq_of_veq <| by
    fin_cases x <;> simp <;> exact rfl
  right_inv := fun x => by
    fin_cases x <;> simp <;> exact rfl

def fin11Fin1Equiv: Fin (1 * 1) ≃ Fin 1
    where
  toFun x := match x with
    | ⟨0, _⟩ => 0
  invFun x:= match x with
    | 0 => ⟨0, zero_lt_one⟩
  left_inv := fun x => Fin.eq_of_veq <| by
    fin_cases x
    simp
  right_inv := fun x => by
    fin_cases x
    simp

abbrev flatten_2q (M: Matrix (Fin 2 × Fin 2) (Fin 1 × Fin 1) ℂ): (Matrix (Fin 4) (Fin 1) ℂ) :=
    reindex (trans finProdFinEquiv fin22Fin4Equiv) (trans finProdFinEquiv fin11Fin1Equiv) M
