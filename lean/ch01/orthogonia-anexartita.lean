-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Orthogonal Sets Are Linearly Independent · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.OrthogoniaAnexartita
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem independent {k : ℕ} (v : Fin k → V) (hz : ∀ i, v i ≠ 0)
    (ho : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℝ = 0) : LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h1 : ⟪v j, ∑ i, c i • v i⟫_ℝ = 0 := by rw [hc, inner_zero_right]
  rw [inner_sum] at h1
  simp only [real_inner_smul_right] at h1
  rw [Finset.sum_eq_single j] at h1
  · have h2 : ⟪v j, v j⟫_ℝ ≠ 0 := inner_self_ne_zero.mpr (hz j)
    exact (mul_eq_zero.mp h1).resolve_right h2
  · intro i _ hij
    rw [ho j i (Ne.symm hij), mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem orthonormal_independent {k : ℕ} (v : Fin k → V) (hv : Orthonormal ℝ v) :
    LinearIndependent ℝ v := by
  apply independent v
  · intro i h
    have h1 := hv.1 i
    rw [h, norm_zero] at h1
    norm_num at h1
  · intro i j hij
    exact hv.2 hij

end Ch1.OrthogoniaAnexartita
