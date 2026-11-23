-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 3 · Non-trivial Solutions of a Homogeneous System · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch3.OmogenesSystima
open Matrix Module

variable {m n : ℕ}

theorem nonzero_of_rank_lt (A : Matrix (Fin m) (Fin n) ℝ) (h : A.rank < n) :
    ∃ x : Fin n → ℝ, x ≠ 0 ∧ A *ᵥ x = 0 := by
  have hrn : A.rank + finrank ℝ (LinearMap.ker A.mulVecLin) = n := by
    rw [← finrank_range_mulVecLin, LinearMap.finrank_range_add_finrank_ker, finrank_fin_fun]
  have hk : LinearMap.ker A.mulVecLin ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hrn
    omega
  obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨x, hne, LinearMap.mem_ker.mp hx⟩

theorem multiples (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (hx : A *ᵥ x = 0) (c : ℝ) :
    A *ᵥ (c • x) = 0 := by
  rw [mulVec_smul, hx, smul_zero]

theorem infinitely_many (A : Matrix (Fin m) (Fin n) ℝ) (h : A.rank < n) :
    {x : Fin n → ℝ | A *ᵥ x = 0}.Infinite := by
  obtain ⟨x, hx0, hx⟩ := nonzero_of_rank_lt A h
  exact Set.infinite_of_injective_forall_mem (smul_left_injective ℝ hx0)
    (fun c => multiples A x hx c)

theorem zero_of_rank_eq (A : Matrix (Fin m) (Fin n) ℝ) (h : A.rank = n) (x : Fin n → ℝ)
    (hx : A *ᵥ x = 0) : x = 0 := by
  have hrn : A.rank + finrank ℝ (LinearMap.ker A.mulVecLin) = n := by
    rw [← finrank_range_mulVecLin, LinearMap.finrank_range_add_finrank_ker, finrank_fin_fun]
  have hk : LinearMap.ker A.mulVecLin = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    omega
  have hmem : x ∈ LinearMap.ker A.mulVecLin := LinearMap.mem_ker.mpr hx
  rw [hk, Submodule.mem_bot] at hmem
  exact hmem

theorem full_rank_needs (A : Matrix (Fin m) (Fin n) ℝ) (h : A.rank = n) : n ≤ m := by
  have hr : A.rank ≤ m := by simpa using A.rank_le_card_height
  omega

theorem square_iff (A : Matrix (Fin n) (Fin n) ℝ) :
    (∀ x, A *ᵥ x = 0 → x = 0) ↔ A.det ≠ 0 := by
  rw [← not_iff_not, not_not, ← exists_mulVec_eq_zero_iff]
  push Not
  constructor
  · rintro ⟨x, h1, h2⟩
    exact ⟨x, h2, h1⟩
  · rintro ⟨x, h1, h2⟩
    exact ⟨x, h2, h1⟩

end Ch3.OmogenesSystima
