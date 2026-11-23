-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 2 · The Characteristic Polynomial · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch2.XaraktiristikoPolyonymo
open Matrix Polynomial

variable {n : ℕ}

theorem eigen_iff_det (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    (∃ v : Fin n → ℂ, v ≠ 0 ∧ A *ᵥ v = μ • v) ↔
      (A - μ • (1 : Matrix (Fin n) (Fin n) ℂ)).det = 0 := by
  rw [← exists_mulVec_eq_zero_iff]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero]

theorem charpoly_eval (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    A.charpoly.eval μ = (-1) ^ n * (A - μ • (1 : Matrix (Fin n) (Fin n) ℂ)).det := by
  have h : Matrix.scalar (Fin n) μ - A = -(A - μ • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [neg_sub, scalar_apply, smul_one_eq_diagonal]
  rw [eval_charpoly, h, det_neg, Fintype.card_fin]

theorem eigen_iff_root (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    (∃ v : Fin n → ℂ, v ≠ 0 ∧ A *ᵥ v = μ • v) ↔ A.charpoly.IsRoot μ := by
  rw [eigen_iff_det, IsRoot.def, charpoly_eval]
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (by norm_num))

theorem degree (A : Matrix (Fin n) (Fin n) ℂ) : A.charpoly.natDegree = n := by
  rw [charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem conj_root (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℂ)
    (h : (A.map (algebraMap ℝ ℂ)).charpoly.IsRoot μ) :
    (A.map (algebraMap ℝ ℂ)).charpoly.IsRoot (starRingEnd ℂ μ) := by
  rw [charpoly_map, IsRoot.def, eval_map_algebraMap] at h ⊢
  rw [← Complex.conjAe_coe, aeval_algHom_apply, h, map_zero]

end Ch2.XaraktiristikoPolyonymo
