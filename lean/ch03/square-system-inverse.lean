-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 3 · Square System — Solution via the Inverse · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch3.TetragonikoSystima
open Matrix Module

variable {n : ℕ}

theorem det_iff_rank (A : Matrix (Fin n) (Fin n) ℝ) : A.det ≠ 0 ↔ A.rank = n := by
  constructor
  · intro h
    have := A.rank_of_isUnit ((isUnit_iff_isUnit_det A).mpr h.isUnit)
    simpa using this
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

theorem unique_solution (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (b x : Fin n → ℝ) :
    A *ᵥ x = b ↔ x = A⁻¹ *ᵥ b := by
  constructor
  · intro h
    rw [← h]
    rw [mulVec_mulVec]
    rw [nonsing_inv_mul A hA.isUnit]
    rw [one_mulVec]
  · intro h
    rw [h]
    rw [mulVec_mulVec]
    rw [mul_nonsing_inv A hA.isUnit]
    rw [one_mulVec]

theorem solves (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (b : Fin n → ℝ) :
    A *ᵥ (A⁻¹ *ᵥ b) = b := by
  rw [mulVec_mulVec, mul_nonsing_inv A hA.isUnit, one_mulVec]

end Ch3.TetragonikoSystima
