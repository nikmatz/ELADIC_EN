-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 0 · Properties of the Dot Product · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch0.EsotGinomeno
open scoped InnerProductSpace

variable {n : ℕ}

theorem comm (u v : Fin n → ℝ) : u ⬝ᵥ v = v ⬝ᵥ u := by
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm (u i) (v i)

theorem add_right (u v w : Fin n → ℝ) : u ⬝ᵥ (v + w) = u ⬝ᵥ v + u ⬝ᵥ w := by
  simp only [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem smul_left (c : ℝ) (u v : Fin n → ℝ) : (c • u) ⬝ᵥ v = c * (u ⬝ᵥ v) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem self_nonneg (u : Fin n → ℝ) : 0 ≤ u ⬝ᵥ u := by
  unfold dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))

theorem self_eq_zero (u : Fin n → ℝ) : u ⬝ᵥ u = 0 ↔ u = 0 := dotProduct_self_eq_zero

theorem self_eq_norm_sq (u : EuclideanSpace ℝ (Fin n)) : ⟪u, u⟫_ℝ = ‖u‖ ^ 2 :=
  real_inner_self_eq_norm_sq u

theorem geometric (u v : EuclideanSpace ℝ (Fin n)) :
    ⟪u, v⟫_ℝ = ‖u‖ * ‖v‖ * Real.cos (InnerProductGeometry.angle u v) := by
  rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm u v]
  ring

end Ch0.EsotGinomeno
