import Mathlib.LinearAlgebra.Matrix.Hermitian

open Complex

def PauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

abbrev my_im: ℂ := ⟨0, 1⟩

def PauliY : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I; I, 0]

def PauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

theorem PauliX_is_hermitian: PauliX.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [PauliX]
