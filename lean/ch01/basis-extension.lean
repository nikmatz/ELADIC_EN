-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Extension to a Basis · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.EpektasiBasis
open Module Submodule

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem extend (S : Set V) (hS : LinearIndepOn ℝ id S) :
    ∃ B : Set V, S ⊆ B ∧ LinearIndepOn ℝ id B ∧ span ℝ B = ⊤ := by
  obtain ⟨B, -, hSB, hspan, hB⟩ := exists_linearIndepOn_extension hS (Set.subset_univ S)
  refine ⟨B, hSB, hB, ?_⟩
  simpa using hspan

end Ch1.EpektasiBasis
