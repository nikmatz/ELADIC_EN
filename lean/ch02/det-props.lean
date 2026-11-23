-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 2 · Properties of the Determinant · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch2.IdiotitesOrizousas
open Matrix

variable {n : ℕ}

theorem det_of_mul (A B : Matrix (Fin n) (Fin n) ℝ) : (A * B).det = A.det * B.det :=
  det_mul A B

theorem det_of_transpose (A : Matrix (Fin n) (Fin n) ℝ) : Aᵀ.det = A.det :=
  det_transpose A

theorem det_of_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : (c • A).det = c ^ n * A.det := by
  rw [det_smul, Fintype.card_fin]

theorem invertible_iff (A : Matrix (Fin n) (Fin n) ℝ) : IsUnit A ↔ A.det ≠ 0 := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

theorem det_of_swap (A : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n} (h : i ≠ j) :
    (A.submatrix (Equiv.swap i j) id).det = -A.det := by
  rw [det_permute, Equiv.Perm.sign_swap h]
  simp

theorem det_of_add_row (A : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n} (h : i ≠ j) (c : ℝ) :
    (A.updateRow i (A i + c • A j)).det = A.det :=
  det_updateRow_add_smul_self A h c

theorem det_of_equal_rows (A : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n} (h : i ≠ j)
    (hij : A i = A j) : A.det = 0 :=
  det_zero_of_row_eq h hij

end Ch2.IdiotitesOrizousas
