-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 2 · Determinant of a Triangular Matrix · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch2.OrizousaTrigonikou
open Matrix

variable {n : ℕ}

theorem det_upper (A : Matrix (Fin n) (Fin n) ℝ) (h : ∀ i j, j < i → A i j = 0) :
    A.det = ∏ i, A i i :=
  det_of_isUpperTriangular (fun i j hij => h i j hij)

theorem det_lower (A : Matrix (Fin n) (Fin n) ℝ) (h : ∀ i j, i < j → A i j = 0) :
    A.det = ∏ i, A i i :=
  det_of_isLowerTriangular A (fun i j hij => h i j hij)

theorem det_diag (d : Fin n → ℝ) : (diagonal d).det = ∏ i, d i :=
  det_diagonal

end Ch2.OrizousaTrigonikou
