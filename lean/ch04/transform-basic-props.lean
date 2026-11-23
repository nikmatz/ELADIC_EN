-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 4 · Basic Properties of a Linear Transformation · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch4.VasikesIdiotites

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem image_zero (T : V →ₗ[ℝ] W) : T 0 = 0 := by
  have h : T 0 + T 0 = T 0 + 0 := by
    rw [← map_add]
    rw [add_zero, add_zero]
  rw [add_right_inj] at h
  exact h

theorem image_neg (T : V →ₗ[ℝ] W) (u : V) : T (-u) = -T u := by
  rw [← neg_one_smul ℝ u, map_smul, neg_one_smul]

theorem image_lincomb (T : V →ₗ[ℝ] W) (k : ℕ) (c : Fin k → ℝ) (u : Fin k → V) :
    T (∑ i, c i • u i) = ∑ i, c i • T (u i) := by
  rw [map_sum]
  simp only [map_smul]

end Ch4.VasikesIdiotites
