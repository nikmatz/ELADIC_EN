-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Properties of the Scalar Triple Product · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.MiktoGinomeno
open Matrix

theorem eq_det (u v w : Fin 3 → ℝ) : (u ⨯₃ v) ⬝ᵥ w = Matrix.det ![u, v, w] := by
  rw [dotProduct_comm, triple_product_permutation, triple_product_eq_det]

theorem cyclic (u v w : Fin 3 → ℝ) : (u ⨯₃ v) ⬝ᵥ w = (v ⨯₃ w) ⬝ᵥ u := by
  rw [dotProduct_comm, triple_product_permutation, dotProduct_comm]

theorem swap (u v w : Fin 3 → ℝ) : (v ⨯₃ u) ⬝ᵥ w = -((u ⨯₃ v) ⬝ᵥ w) := by
  rw [← cross_anticomm, neg_dotProduct]

theorem independent_iff_det (a b c : Fin 3 → ℝ) :
    LinearIndependent ℝ ![a, b, c] ↔ Matrix.det ![a, b, c] ≠ 0 :=
  (Matrix.linearIndependent_row_iff (A := Matrix.of ![a, b, c])).trans
    Matrix.nonsingular_iff_det_ne_zero

theorem zero_iff (u v w : Fin 3 → ℝ) :
    (u ⨯₃ v) ⬝ᵥ w = 0 ↔ ¬ LinearIndependent ℝ ![u, v, w] := by
  rw [eq_det, independent_iff_det, not_not]

end Ch1.MiktoGinomeno
