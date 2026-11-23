-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 5 · Relation Between the Multiplicities · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch5.SxesiPollaplotiton
open Matrix

variable {n : ℕ}

theorem geom_le_alg (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) :
    Module.finrank ℝ (Module.End.eigenspace (toLin' A) μ) ≤ A.charpoly.rootMultiplicity μ := by
  rw [← charpoly_toLin' A]
  exact LinearMap.finrank_eigenspace_le (toLin' A) μ

theorem one_le_geom (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) (v : Fin n → ℝ) (hv : v ≠ 0)
    (h : A *ᵥ v = μ • v) : 1 ≤ Module.finrank ℝ (Module.End.eigenspace (toLin' A) μ) := by
  rw [Submodule.one_le_finrank_iff, Submodule.ne_bot_iff]
  refine ⟨v, ?_, hv⟩
  rw [Module.End.mem_eigenspace_iff, toLin'_apply]
  exact h

end Ch5.SxesiPollaplotiton
