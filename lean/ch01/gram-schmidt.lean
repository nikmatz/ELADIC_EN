-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · The Gram–Schmidt Algorithm · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.GramSchmidt
open scoped InnerProductSpace
open InnerProductSpace Submodule

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem orthogonal {k : ℕ} (v : Fin k → V) {i j : Fin k} (h : i ≠ j) :
    ⟪gramSchmidt ℝ v i, gramSchmidt ℝ v j⟫_ℝ = 0 :=
  gramSchmidt_orthogonal ℝ v h

theorem same_span {k : ℕ} (v : Fin k → V) :
    span ℝ (Set.range (gramSchmidt ℝ v)) = span ℝ (Set.range v) :=
  span_gramSchmidt ℝ v

theorem orthonormal {k : ℕ} (v : Fin k → V) (h : LinearIndependent ℝ v) :
    Orthonormal ℝ (gramSchmidtNormed ℝ v) :=
  gramSchmidtNormed_orthonormal h

end Ch1.GramSchmidt
