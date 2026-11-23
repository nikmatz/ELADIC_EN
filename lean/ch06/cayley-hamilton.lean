-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 6 · The Cayley–Hamilton Theorem · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch6.CayleyHamilton
open Matrix Polynomial

variable {n : ℕ}

theorem cayley_hamilton (A : Matrix (Fin n) (Fin n) ℝ) : aeval A A.charpoly = 0 :=
  aeval_self_charpoly A

theorem book_version (A : Matrix (Fin n) (Fin n) ℝ) :
    aeval A ((-1 : ℝ[X]) ^ n * A.charpoly) = 0 := by
  rw [map_mul, cayley_hamilton A, mul_zero]

theorem two_by_two (A : Matrix (Fin 2) (Fin 2) ℝ) :
    A ^ 2 - A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
  have h := cayley_hamilton A
  rw [charpoly_fin_two, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, aeval_C,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_one_mul] at h
  exact h

end Ch6.CayleyHamilton
