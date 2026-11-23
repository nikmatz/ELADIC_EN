-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Direct Sums and Dimension · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.EuthuAthroisma
open Module Submodule

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem dim_direct (U W : Submodule ℝ V) (h : U ⊓ W = ⊥) :
    finrank ℝ ↥(U ⊔ W) = finrank ℝ U + finrank ℝ W := by
  have := finrank_sup_add_finrank_inf_eq U W
  rw [h, finrank_bot] at this
  simpa using this

theorem direct_sum_iff (U W : Submodule ℝ V) :
    IsCompl U W ↔ U ⊓ W = ⊥ ∧ finrank ℝ U + finrank ℝ W = finrank ℝ V := by
  constructor
  · intro h
    refine ⟨h.inf_eq_bot, ?_⟩
    rw [← dim_direct U W h.inf_eq_bot, h.sup_eq_top, finrank_top]
  · rintro ⟨h₁, h₂⟩
    refine ⟨disjoint_iff.mpr h₁, codisjoint_iff.mpr ?_⟩
    apply eq_top_of_finrank_eq
    rw [dim_direct U W h₁, h₂]

end Ch1.EuthuAthroisma
