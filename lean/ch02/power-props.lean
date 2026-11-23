-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 2 · Properties of Powers · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch2.DynameisPinaka
open Matrix

variable {n : ℕ}

theorem zpow_add_rule (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (p q : ℤ) :
    A ^ p * A ^ q = A ^ (p + q) :=
  (Matrix.zpow_add hA.isUnit p q).symm

theorem zpow_mul_rule (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (p q : ℤ) :
    (A ^ p) ^ q = A ^ (p * q) :=
  (Matrix.zpow_mul A hA.isUnit p q).symm

theorem counterexample :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A ∧ (A * B) ^ 2 ≠ A ^ 2 * B ^ 2 := by
  refine ⟨!![1, 1; 0, 1], !![1, 0; 1, 1], ?_, ?_⟩
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    norm_num [sq, Matrix.mul_apply, Fin.sum_univ_two] at h01

end Ch2.DynameisPinaka
