-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 3 · Cramer's Rule · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch3.Cramer
open Matrix

variable {n : ℕ}

theorem cramer_solution (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (hA : A.det ≠ 0)
    (x : Fin n → ℝ) : A *ᵥ x = b ↔ ∀ i, x i = (A.updateCol i b).det / A.det := by
  have key : A *ᵥ (A.det⁻¹ • cramer A b) = b := by
    rw [mulVec_smul, mulVec_cramer, smul_smul, inv_mul_cancel₀ hA, one_smul]
  have hx₀ : A.det⁻¹ • cramer A b = fun i => (A.updateCol i b).det / A.det := by
    funext i
    rw [Pi.smul_apply, cramer_apply, smul_eq_mul, div_eq_inv_mul]
  rw [hx₀] at key
  constructor
  · intro h i
    have h2 : A *ᵥ (x - fun i => (A.updateCol i b).det / A.det) = 0 := by
      rw [mulVec_sub, h, key, sub_self]
    have h3 : (x - fun i => (A.updateCol i b).det / A.det) = 0 := by
      by_contra hne
      exact hA (exists_mulVec_eq_zero_iff.mp ⟨_, hne, h2⟩)
    rw [sub_eq_zero] at h3
    rw [h3]
  · intro h
    have hx : x = fun i => (A.updateCol i b).det / A.det := funext h
    rw [hx, key]

end Ch3.Cramer
