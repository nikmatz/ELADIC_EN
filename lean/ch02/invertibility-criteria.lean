-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 2 · Criteria for Invertibility · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch2.KritiriaAntistrepsimotitas
open Matrix Module

variable {n : ℕ}

theorem unit_iff_det (A : Matrix (Fin n) (Fin n) ℝ) : IsUnit A ↔ A.det ≠ 0 := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

theorem rank_iff_det (A : Matrix (Fin n) (Fin n) ℝ) : A.rank = n ↔ A.det ≠ 0 := by
  constructor
  · intro h hdet
    obtain ⟨x, hx, hAx⟩ := exists_mulVec_eq_zero_iff.mpr hdet
    have hrn : A.rank + finrank ℝ (LinearMap.ker A.mulVecLin) = n := by
      rw [← finrank_range_mulVecLin, LinearMap.finrank_range_add_finrank_ker, finrank_fin_fun]
    have hk : LinearMap.ker A.mulVecLin = ⊥ := by
      rw [← Submodule.finrank_eq_zero]
      omega
    have hmem : x ∈ LinearMap.ker A.mulVecLin := LinearMap.mem_ker.mpr hAx
    rw [hk, Submodule.mem_bot] at hmem
    exact hx hmem
  · intro h
    have := A.rank_of_isUnit ((unit_iff_det A).mpr h)
    simpa using this

theorem cols_iff_det (A : Matrix (Fin n) (Fin n) ℝ) : LinearIndependent ℝ A.col ↔ A.det ≠ 0 :=
  linearIndependent_col_iff.trans nonsingular_iff_det_ne_zero

theorem rows_iff_det (A : Matrix (Fin n) (Fin n) ℝ) : LinearIndependent ℝ A.row ↔ A.det ≠ 0 :=
  linearIndependent_row_iff.trans nonsingular_iff_det_ne_zero

end Ch2.KritiriaAntistrepsimotitas
