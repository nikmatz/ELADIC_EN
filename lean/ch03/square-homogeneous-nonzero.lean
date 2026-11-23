-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 3 · Non-trivial Solutions of a Square Homogeneous System · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch3.TetragonikoOmogenes
open Matrix Module

variable {m n : ℕ}

theorem nonzero_iff_det (A : Matrix (Fin n) (Fin n) ℝ) :
    (∃ x : Fin n → ℝ, x ≠ 0 ∧ A *ᵥ x = 0) ↔ A.det = 0 :=
  exists_mulVec_eq_zero_iff

theorem more_unknowns (A : Matrix (Fin m) (Fin n) ℝ) (h : m < n) :
    ∃ x : Fin n → ℝ, x ≠ 0 ∧ A *ᵥ x = 0 := by
  have hr : A.rank ≤ m := by simpa using A.rank_le_card_height
  have hrn : A.rank + finrank ℝ (LinearMap.ker A.mulVecLin) = n := by
    rw [← finrank_range_mulVecLin, LinearMap.finrank_range_add_finrank_ker, finrank_fin_fun]
  have hk : LinearMap.ker A.mulVecLin ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hrn
    omega
  obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨x, hne, LinearMap.mem_ker.mp hx⟩

end Ch3.TetragonikoOmogenes
