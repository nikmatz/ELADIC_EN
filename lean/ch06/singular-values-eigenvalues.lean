-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 6 · Singular Values from the Eigenvalues of AᵀA · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch6.IdiazousesTimes
open LinearMap Module

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem singular_sqrt (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (i : Fin n) :
    T.singularValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn i) :=
  T.singularValues_fin hn i

theorem singular_sq (T : E →ₗ[ℝ] F) {n : ℕ} (hn : finrank ℝ E = n) (i : Fin n) :
    T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn i :=
  T.sq_singularValues_fin hn i

theorem antitone_singular (T : E →ₗ[ℝ] F) : Antitone T.singularValues :=
  T.singularValues_antitone

theorem singular_pos_iff (T : E →ₗ[ℝ] F) (i : ℕ) :
    0 < T.singularValues i ↔ i < finrank ℝ (range T) :=
  T.singularValues_pos_iff_lt_finrank_range

theorem singular_zero_iff (T : E →ₗ[ℝ] F) (i : ℕ) :
    T.singularValues i = 0 ↔ finrank ℝ (range T) ≤ i :=
  T.singularValues_eq_zero_iff_le_finrank_range

end Ch6.IdiazousesTimes
