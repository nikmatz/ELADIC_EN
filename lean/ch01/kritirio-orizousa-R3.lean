-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Determinant Test for Three Vectors in ℝ³ · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.KritirioOrizousas
open Matrix

theorem independent_iff_det (A : Matrix (Fin 3) (Fin 3) ℝ) :
    LinearIndependent ℝ A.col ↔ A.det ≠ 0 :=
  linearIndependent_col_iff.trans nonsingular_iff_det_ne_zero

end Ch1.KritirioOrizousas
