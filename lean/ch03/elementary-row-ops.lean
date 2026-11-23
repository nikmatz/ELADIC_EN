-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 3 · Elementary Row Operations · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch3.StoixeiodeisMetasximatismoi
open Matrix

variable {m n : ℕ}

theorem same_solutions (E : Matrix (Fin m) (Fin m) ℝ) (hE : E.det ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    A *ᵥ x = b ↔ (E * A) *ᵥ x = E *ᵥ b := by
  rw [← mulVec_mulVec]
  constructor
  · intro h
    rw [h]
  · intro h
    have h2 : E⁻¹ *ᵥ (E *ᵥ (A *ᵥ x)) = E⁻¹ *ᵥ (E *ᵥ b) := by rw [h]
    rw [mulVec_mulVec (A *ᵥ x) E⁻¹ E, mulVec_mulVec b E⁻¹ E, nonsing_inv_mul E hE.isUnit,
      one_mulVec, one_mulVec] at h2
    exact h2

theorem swap_invertible (i j : Fin m) (h : i ≠ j) :
    ((Equiv.swap i j).permMatrix ℝ).det ≠ 0 := by
  rw [det_permutation, Equiv.Perm.sign_swap h]
  norm_num

theorem scale_invertible (i : Fin m) (c : ℝ) (hc : c ≠ 0) :
    (diagonal (Function.update (fun _ => (1 : ℝ)) i c)).det ≠ 0 := by
  rw [det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
  simpa using hc

theorem add_row_invertible (i j : Fin m) (h : i ≠ j) (c : ℝ) :
    (transvection i j c).det ≠ 0 := by
  rw [det_transvection_of_ne i j h c]
  exact one_ne_zero

end Ch3.StoixeiodeisMetasximatismoi
