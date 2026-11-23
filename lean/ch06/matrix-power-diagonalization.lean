-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 6 · Computing the Power A^k by Diagonalization · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch6.DynamiPinaka
open Matrix

variable {n : ℕ}

theorem conj_pow (P D : Matrix (Fin n) (Fin n) ℝ) (hP : P.det ≠ 0) (k : ℕ) :
    (P * D * P⁻¹) ^ k = P * D ^ k * P⁻¹ := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, mul_one, mul_nonsing_inv P hP.isUnit]
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul_cancel_left P _ hP.isUnit]
    rw [← Matrix.mul_assoc (D ^ k), ← pow_succ]

theorem pow_diagonal (A P : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (hP : P.det ≠ 0)
    (hA : A = P * diagonal d * P⁻¹) (k : ℕ) :
    A ^ k = P * diagonal (fun i => d i ^ k) * P⁻¹ := by
  rw [hA, conj_pow P (diagonal d) hP k, diagonal_pow, Pi.pow_def]

end Ch6.DynamiPinaka
