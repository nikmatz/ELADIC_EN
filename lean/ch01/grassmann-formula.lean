-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Grassmann's Formula · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.Grassmann
open Module Submodule

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem sum_form (U W : Submodule ℝ V) :
    finrank ℝ ↥(U ⊔ W) + finrank ℝ ↥(U ⊓ W) = finrank ℝ U + finrank ℝ W :=
  finrank_sup_add_finrank_inf_eq U W

theorem grassmann (U W : Submodule ℝ V) :
    finrank ℝ ↥(U ⊔ W) = finrank ℝ U + finrank ℝ W - finrank ℝ ↥(U ⊓ W) := by
  have := sum_form U W
  omega

end Ch1.Grassmann
