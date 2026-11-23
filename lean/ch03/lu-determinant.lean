-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 3 · Connection between LU and the Determinant · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch3.OrizousaLU
open Matrix

variable {n : ℕ}

theorem det_L (L : Matrix (Fin n) (Fin n) ℝ) (hL : ∀ i j, i < j → L i j = 0)
    (h1 : ∀ i, L i i = 1) : L.det = 1 := by
  rw [det_of_isLowerTriangular L (fun i j hij => hL i j hij)]
  simp [h1]

theorem det_LU (L U : Matrix (Fin n) (Fin n) ℝ) (hL : ∀ i j, i < j → L i j = 0)
    (h1 : ∀ i, L i i = 1) (hU : ∀ i j, j < i → U i j = 0) :
    (L * U).det = ∏ i, U i i := by
  rw [det_mul]
  rw [det_L L hL h1]
  rw [one_mul]
  exact det_of_isUpperTriangular (fun i j hij => hU i j hij)

end Ch3.OrizousaLU
