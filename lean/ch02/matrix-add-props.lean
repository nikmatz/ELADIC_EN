-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 2 · Properties of Addition and Scalar Multiplication · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch2.PrakseisPinakon
open Matrix Module

variable {m n : ℕ}

theorem add_commutes (A B : Matrix (Fin m) (Fin n) ℝ) : A + B = B + A := by
  ext i j
  rw [Matrix.add_apply, Matrix.add_apply]
  exact add_comm (A i j) (B i j)

theorem add_associates (A B C : Matrix (Fin m) (Fin n) ℝ) : A + (B + C) = (A + B) + C := by
  ext i j
  simp only [Matrix.add_apply]
  ring

theorem add_zero_matrix (A : Matrix (Fin m) (Fin n) ℝ) : A + 0 = A := by
  ext i j
  simp only [Matrix.add_apply, Matrix.zero_apply, add_zero]

theorem add_opposite (A : Matrix (Fin m) (Fin n) ℝ) : A + (-A) = 0 := by
  ext i j
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.zero_apply, add_neg_cancel]

theorem smul_add_scalars (a b : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    (a + b) • A = a • A + b • A := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem smul_add_matrices (a : ℝ) (A B : Matrix (Fin m) (Fin n) ℝ) :
    a • (A + B) = a • A + a • B := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem smul_smul_matrix (a b : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) : a • (b • A) = (a * b) • A := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem one_smul_matrix (A : Matrix (Fin m) (Fin n) ℝ) : (1 : ℝ) • A = A := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, one_mul]

theorem dimension : finrank ℝ (Matrix (Fin m) (Fin n) ℝ) = m * n := by
  simp [finrank_matrix]

end Ch2.PrakseisPinakon
