-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 2 · Rank–Nullity Theorem for Matrices · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch2.TaksiMidenoxoros
open Matrix Module

variable {m n : ℕ}

theorem row_rank_eq_col_rank (A : Matrix (Fin m) (Fin n) ℝ) : Aᵀ.rank = A.rank :=
  rank_transpose A

theorem rank_nullity (A : Matrix (Fin m) (Fin n) ℝ) :
    A.rank + finrank ℝ (LinearMap.ker A.mulVecLin) = n := by
  rw [← finrank_range_mulVecLin, LinearMap.finrank_range_add_finrank_ker, finrank_fin_fun]

theorem rank_nullity_transpose (A : Matrix (Fin m) (Fin n) ℝ) :
    A.rank + finrank ℝ (LinearMap.ker Aᵀ.mulVecLin) = m := by
  rw [← rank_transpose A, ← finrank_range_mulVecLin, LinearMap.finrank_range_add_finrank_ker,
    finrank_fin_fun]

theorem col_perp_null_transpose (A : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) (w : Fin m → ℝ)
    (hw : Aᵀ *ᵥ w = 0) : (A *ᵥ v) ⬝ᵥ w = 0 := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hw, zero_dotProduct]

theorem row_perp_null (A : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) (w : Fin m → ℝ)
    (hv : A *ᵥ v = 0) : (Aᵀ *ᵥ w) ⬝ᵥ v = 0 := by
  rw [mulVec_transpose, ← dotProduct_mulVec, hv, dotProduct_zero]

end Ch2.TaksiMidenoxoros
