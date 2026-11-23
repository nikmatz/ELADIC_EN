-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 2 · Properties of the Inverse Matrix · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch2.IdiotitesAntistrofou
open Matrix

variable {n : ℕ}

theorem inv_of_inv (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) : A⁻¹⁻¹ = A := by
  apply inv_eq_right_inv
  exact nonsing_inv_mul A hA.isUnit

theorem inv_of_mul (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  apply inv_eq_right_inv
  rw [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc B]
  rw [mul_nonsing_inv B hB.isUnit]
  rw [Matrix.one_mul]
  exact mul_nonsing_inv A hA.isUnit

theorem inv_of_transpose (A : Matrix (Fin n) (Fin n) ℝ) : Aᵀ⁻¹ = A⁻¹ᵀ :=
  (transpose_nonsing_inv A).symm

theorem det_of_inv (A : Matrix (Fin n) (Fin n) ℝ) : A⁻¹.det = 1 / A.det := by
  rw [det_nonsing_inv, Ring.inverse_eq_inv, one_div]

theorem inv_of_smul (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    (c • A)⁻¹ = (1 / c) • A⁻¹ := by
  apply inv_eq_right_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, one_div, mul_inv_cancel₀ hc, one_smul,
    mul_nonsing_inv A hA.isUnit]

theorem inv_of_diagonal (d : Fin n → ℝ) (h : ∀ i, d i ≠ 0) :
    (diagonal d)⁻¹ = diagonal (fun i => 1 / d i) := by
  apply inv_eq_right_inv
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  rw [mul_one_div_cancel (h i)]

end Ch2.IdiotitesAntistrofou
