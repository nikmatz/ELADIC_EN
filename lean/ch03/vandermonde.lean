-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 3 · The Vandermonde Matrix and Interpolation · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch3.Vandermonde
open Matrix

variable {n : ℕ}

theorem entry (x : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) : vandermonde x i j = x i ^ (j : ℕ) :=
  vandermonde_apply x i j

theorem system_row (x a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (vandermonde x *ᵥ a) i = ∑ j, a j * x i ^ (j : ℕ) := by
  simp only [mulVec, dotProduct, vandermonde_apply]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

theorem det_ne_zero (x : Fin (n + 1) → ℝ) (hx : Function.Injective x) :
    (vandermonde x).det ≠ 0 :=
  det_vandermonde_ne_zero_iff.mpr hx

theorem unique_coeffs (x : Fin (n + 1) → ℝ) (hx : Function.Injective x) (y : Fin (n + 1) → ℝ) :
    ∃! a : Fin (n + 1) → ℝ, vandermonde x *ᵥ a = y := by
  have hV := det_ne_zero x hx
  refine ExistsUnique.intro ((vandermonde x)⁻¹ *ᵥ y) ?_ ?_
  · rw [mulVec_mulVec, mul_nonsing_inv _ hV.isUnit, one_mulVec]
  · intro a ha
    rw [← ha, mulVec_mulVec, nonsing_inv_mul _ hV.isUnit, one_mulVec]

end Ch3.Vandermonde
