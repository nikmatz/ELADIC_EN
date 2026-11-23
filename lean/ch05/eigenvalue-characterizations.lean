-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 5 · Equivalent Characterizations of an Eigenvalue · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch5.XaraktirismoiIdiotimis
open Matrix

variable {n : ℕ}

theorem eigen_eq_iff (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) (v : Fin n → ℝ) :
    A *ᵥ v = μ • v ↔ (A - μ • 1) *ᵥ v = 0 := by
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]

theorem i_iff_ii (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) :
    (∃ v : Fin n → ℝ, v ≠ 0 ∧ A *ᵥ v = μ • v) ↔ (A - μ • 1).det = 0 := by
  rw [← exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    rw [eigen_eq_iff] at h
    exact ⟨v, hv, h⟩
  · rintro ⟨v, hv, h⟩
    rw [← eigen_eq_iff] at h
    exact ⟨v, hv, h⟩

theorem ii_iff_iii (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) :
    (A - μ • 1).det = 0 ↔ ¬ IsUnit (A - μ • 1) := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]

theorem i_iff_iv (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) :
    (∃ v : Fin n → ℝ, v ≠ 0 ∧ A *ᵥ v = μ • v) ↔ LinearMap.ker (A - μ • 1).mulVecLin ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨v, ?_, hv⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, ← eigen_eq_iff]
    exact h
  · rintro ⟨v, hk, hv⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, ← eigen_eq_iff] at hk
    exact ⟨v, hv, hk⟩

theorem characterizations (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) : List.TFAE [
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ A *ᵥ v = μ • v,
    (A - μ • 1).det = 0,
    ¬ IsUnit (A - μ • 1),
    LinearMap.ker (A - μ • 1).mulVecLin ≠ ⊥] := by
  tfae_have 1 ↔ 2 := i_iff_ii A μ
  tfae_have 2 ↔ 3 := ii_iff_iii A μ
  tfae_have 1 ↔ 4 := i_iff_iv A μ
  tfae_finish

end Ch5.XaraktirismoiIdiotimis
