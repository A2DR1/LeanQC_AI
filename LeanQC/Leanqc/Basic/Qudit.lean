import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Kronecker
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Star.Unitary
import Mathlib.Logic.Equiv.Fin

import Leanqc.Util.Math
-- import LeanCopilot

open Matrix
open Kronecker
open Complex

namespace Quantum

/--
Pure qudit state of dimension d
-/
def Qudit (d : Nat) := {ψ : Matrix (Fin d) (Fin 1) ℂ // ψᴴ * ψ = 1}

def QuditDual (d : Nat) := {ψ : Matrix (Fin 1) (Fin d) ℂ // ψ * ψᴴ = 1}

def Qudit.dual {d : Nat} (q : Qudit d) : QuditDual d := ⟨q.1ᴴ, by simp; apply q.2⟩

def compose_qudits (q1 : Qudit d1) (q2 : Qudit d2) : Qudit (d1 * d2) :=
 ⟨flatten_kronecker (q1.1 ⊗ₖ q2.1), by
  simp
  rw [conjTranspose_kronecker]
  rw [←mul_kronecker_mul]
  rw [q1.2, q2.2]
  simp⟩

def compose_qudits_dual (q1 : QuditDual d1) (q2 : QuditDual d2) : QuditDual (d1 * d2) :=
 ⟨flatten_kronecker_dual (q1.1 ⊗ₖ q2.1), by
  simp
  rw [conjTranspose_kronecker]
  rw [←mul_kronecker_mul]
  rw [q1.2, q2.2]
  simp⟩

def inner_product {d : Nat} (q1 : Qudit d) (q2 : Qudit d) : ℂ := ((Qudit.dual q1).1 * q2.1) 0 0

/-- Qubit-/
abbrev Qubit := Qudit 2

def Qubit.Zero : Qubit := ⟨!![1; 0], by
   ext i j
   rw [Subsingleton.elim i j, Matrix.mul_apply]
   simp⟩

def Qubit.One : Qubit := ⟨!![0; 1], by
   ext i j
   rw [Subsingleton.elim i j, Matrix.mul_apply]
   simp⟩

/-- Unitary operators on qudits -/
abbrev UnitaryOp (d : Nat) := Matrix.unitaryGroup (Fin d) ℂ

def ApplyUnitaryOp {d : Nat} (U : UnitaryOp d) (q : Qudit d) : Qudit d := ⟨U.1 * q.1, by
  simp [Matrix.mul_assoc]
  rw [←Matrix.mul_assoc]
  calc
    (q.1)ᴴ * (U.1)ᴴ * (U.1 * q.1) = (q.1)ᴴ * (U.1)ᴴ * U.1 * q.1 := by
      rw [←Matrix.mul_assoc]
    _ = (q.1)ᴴ * ((U.1)ᴴ * U.1) * q.1 := by
      rw [←Matrix.mul_assoc]
    _ = (q.1)ᴴ * (1 : Matrix (Fin d) (Fin d) ℂ) * q.1 := by
      congr
      apply And.left (unitary.mem_iff.mp U.2)
    _ = (q.1)ᴴ * q.1 := by
      simp [Matrix.mul_one]
    _ = 1 := by
      apply q.2
  ⟩

def ApplyTwoUnitaryOps {d : Nat} (U1 U2 : UnitaryOp d) (q : Qudit d) : ApplyUnitaryOp U2 (ApplyUnitaryOp U1 q) = ApplyUnitaryOp (U2 * U1) q := by
  simp [ApplyUnitaryOp, Matrix.mul_assoc]

def ApplyIdUnitaryOp {d : Nat} (q : Qudit d) : ApplyUnitaryOp (1: UnitaryOp d) q = q := by
  simp [ApplyUnitaryOp]

theorem composeQuditsConjTranspose {d1 d2 : Nat} (q1 : Qudit d1) (q2 : Qudit d2) :
    Qudit.dual (compose_qudits q1 q2) = compose_qudits_dual (Qudit.dual q1) (Qudit.dual q2) := by
  simp [Qudit.dual, compose_qudits, compose_qudits_dual, conjTranspose_kronecker]

theorem composeInnerProdComm {d1 d2 : Nat} (q1 q2: Qudit d1) (q3 q4: Qudit d2) :
    inner_product (compose_qudits q1 q3) (compose_qudits q2 q4) = inner_product q1 q2 * inner_product q3 q4 := by
  simp [inner_product, composeQuditsConjTranspose, compose_qudits_dual, Qudit.dual, compose_qudits, conjTranspose_kronecker, ←mul_kronecker_mul]
  congr

theorem innerProdUnitary {d : Nat} (U : UnitaryOp d) (q1 q2 : Qudit d) :
    inner_product (ApplyUnitaryOp U q1) (ApplyUnitaryOp U q2) = inner_product q1 q2 := by
  simp [inner_product, ApplyUnitaryOp, Qudit.dual, ←Matrix.mul_assoc]
  rw [Matrix.mul_assoc (q1.1)ᴴ (U.1)ᴴ U.1]
  symm
  calc
    ((q1.1)ᴴ * q2.1) 0 0 = ((q1.1)ᴴ * (1 : Matrix (Fin d) (Fin d) ℂ) * q2.1) 0 0 := by
      rw [Matrix.mul_one]
    _ = ((q1.1)ᴴ * ((U.1)ᴴ * U.1) * q2.1) 0 0 := by
      rw [←(unitary.mem_iff.mp U.2).1]
      congr

theorem innerProdUnitaryConjTranspose {d : Nat} (U : UnitaryOp d) (q1 q2 : Qudit d) :
    inner_product (ApplyUnitaryOp U q1) q2 = inner_product q1 (ApplyUnitaryOp (star U) q2) := by
  simp [inner_product, ApplyUnitaryOp, Qudit.dual, ←Matrix.mul_assoc, star]

-- TODO: handle the extra phase
-- TODO: stronger version --- Qudit
-- TODO: ancilla |ψ00⟩ → |ψψφ⟩
theorem noCloning :
    ¬∃ (U : UnitaryOp 4), ∀ ψ : Qubit, ApplyUnitaryOp U (compose_qudits ψ Qubit.Zero) = compose_qudits ψ ψ := by
  intro u
  rcases u with ⟨U, H⟩
  let φ : Qubit := ⟨!![0.6; 0.8], by
    ext i j
    rw [Subsingleton.elim i j, Matrix.mul_apply]
    simp
    norm_num⟩
  let ψ: Qubit := Qubit.Zero
  have specialize_φ := H φ
  have specialize_ψ := H ψ
  have inner_ψ_φ : inner_product ψ φ = 0.6 := by
    simp [inner_product, Qubit.Zero, φ]
    norm_num
    field_simp
    simp [conjTranspose, Matrix.mul_apply, Qudit.dual,vecHead, vecHead]
  have inner_ψ_φ_sq : (inner_product ψ φ) * (inner_product ψ φ) = 0.36 := by
    simp [inner_ψ_φ]
    norm_num
  have  inner_ψ_φ_ineq : (inner_product ψ φ) * (inner_product ψ φ) ≠ inner_product ψ φ := by
    simp [inner_ψ_φ_sq, inner_product, Qubit.Zero, φ, Qudit.dual, conjTranspose, Matrix.mul_apply, vecHead, vecHead]
    norm_num
  have inner_equal : inner_product (compose_qudits ψ Qubit.Zero) (compose_qudits φ Qubit.Zero) = inner_product ψ φ  := by
    rw [composeInnerProdComm]
    simp [Qubit.Zero, inner_product, Qudit.dual, Matrix.mul_apply]
  have inner_ψ_φ_eq : inner_product ψ φ = (inner_product ψ φ) * (inner_product ψ φ) := by
    calc
      inner_product ψ φ = inner_product (compose_qudits ψ Qubit.Zero) (compose_qudits φ Qubit.Zero) := by rw [←inner_equal]
      _ = inner_product (ApplyUnitaryOp U (compose_qudits ψ Qubit.Zero)) (ApplyUnitaryOp U (compose_qudits φ Qubit.Zero)) := by rw [←innerProdUnitary]
      _ = inner_product (ApplyUnitaryOp U (compose_qudits ψ Qubit.Zero)) (compose_qudits φ φ) := by congr
      _ = inner_product (compose_qudits ψ ψ) (compose_qudits φ φ) := by congr
      _ = inner_product ψ φ * inner_product ψ φ := by rw [composeInnerProdComm]
  exact inner_ψ_φ_ineq inner_ψ_φ_eq.symm

#print noCloning

end Quantum
