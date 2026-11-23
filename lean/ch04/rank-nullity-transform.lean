-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 4 · Rank–Nullity Theorem · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch4.VathmosMidenikotita

variable {m n : ℕ}

theorem dim_ker_add_dim_im (T : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    Module.finrank ℝ (LinearMap.ker T) + Module.finrank ℝ (LinearMap.range T) = n := by
  rw [add_comm, LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]

theorem dim_ker_add_dim_im_general {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] (T : V →ₗ[ℝ] W) :
    Module.finrank ℝ (LinearMap.ker T) + Module.finrank ℝ (LinearMap.range T) =
      Module.finrank ℝ V := by
  rw [add_comm, LinearMap.finrank_range_add_finrank_ker]

end Ch4.VathmosMidenikotita
