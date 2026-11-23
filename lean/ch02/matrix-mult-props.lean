-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 2 · Properties of Matrix Multiplication · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch2.GinomenoPinakon
open Matrix

variable {m n p q : ℕ}

theorem mul_associates (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ)
    (C : Matrix (Fin p) (Fin q) ℝ) : (A * B) * C = A * (B * C) := by
  ext i l
  simp only [Matrix.mul_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

theorem mul_distrib_left (A : Matrix (Fin m) (Fin n) ℝ) (B C : Matrix (Fin n) (Fin p) ℝ) :
    A * (B + C) = A * B + A * C :=
  Matrix.mul_add A B C

theorem mul_distrib_right (A B : Matrix (Fin m) (Fin n) ℝ) (C : Matrix (Fin n) (Fin p) ℝ) :
    (A + B) * C = A * C + B * C :=
  Matrix.add_mul A B C

theorem smul_mul_left (c : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) :
    c • (A * B) = (c • A) * B :=
  (Matrix.smul_mul c A B).symm

theorem smul_mul_right (c : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) :
    c • (A * B) = A * (c • B) :=
  (Matrix.mul_smul A c B).symm

theorem mul_identity (A : Matrix (Fin m) (Fin n) ℝ) :
    A * (1 : Matrix (Fin n) (Fin n) ℝ) = A ∧ (1 : Matrix (Fin m) (Fin m) ℝ) * A = A :=
  ⟨Matrix.mul_one A, Matrix.one_mul A⟩

theorem transpose_of_mul (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin p) ℝ) :
    (A * B)ᵀ = Bᵀ * Aᵀ := by
  ext i j
  rw [Matrix.transpose_apply, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.transpose_apply, Matrix.transpose_apply, mul_comm]

end Ch2.GinomenoPinakon
