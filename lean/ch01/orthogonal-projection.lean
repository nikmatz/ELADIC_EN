-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Orthogonal Projection Theorem · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.OrthogonalProjection
open scoped InnerProductSpace
open Submodule

variable {n : ℕ}

theorem decomposition (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n)) :
    W.starProjection u ∈ W ∧ u - W.starProjection u ∈ Wᗮ :=
  ⟨W.starProjection_apply_mem u, W.sub_starProjection_mem_orthogonal u⟩

theorem unique (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (u p e : EuclideanSpace ℝ (Fin n))
    (hp : p ∈ W) (he : e ∈ Wᗮ) (h : u = p + e) : W.starProjection u = p := by
  apply eq_starProjection_of_mem_of_inner_eq_zero hp
  intro w hw
  rw [h, add_sub_cancel_left]
  exact inner_left_of_mem_orthogonal hw he

theorem closest (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (u w : EuclideanSpace ℝ (Fin n))
    (hw : w ∈ W) : ‖u - W.starProjection u‖ ≤ ‖u - w‖ := by
  set p := W.starProjection u
  have hpw : p - w ∈ W := W.sub_mem (W.starProjection_apply_mem u) hw
  have h0 : ⟪u - p, p - w⟫_ℝ = 0 :=
    inner_left_of_mem_orthogonal hpw (W.sub_starProjection_mem_orthogonal u)
  have pyth := norm_add_sq_eq_norm_sq_add_norm_sq_real h0
  rw [sub_add_sub_cancel] at pyth
  have hsq : ‖u - p‖ ^ 2 ≤ ‖u - w‖ ^ 2 := by nlinarith [mul_self_nonneg ‖p - w‖]
  exact le_of_sq_le_sq hsq (norm_nonneg _)

theorem closest_strict (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (u w : EuclideanSpace ℝ (Fin n))
    (hw : w ∈ W) (hne : w ≠ W.starProjection u) : ‖u - W.starProjection u‖ < ‖u - w‖ := by
  set p := W.starProjection u
  have hpw : p - w ∈ W := W.sub_mem (W.starProjection_apply_mem u) hw
  have h0 : ⟪u - p, p - w⟫_ℝ = 0 :=
    inner_left_of_mem_orthogonal hpw (W.sub_starProjection_mem_orthogonal u)
  have pyth := norm_add_sq_eq_norm_sq_add_norm_sq_real h0
  rw [sub_add_sub_cancel] at pyth
  have hpos : 0 < ‖p - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hsq : ‖u - p‖ ^ 2 < ‖u - w‖ ^ 2 := by nlinarith [mul_pos hpos hpos]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hsq

end Ch1.OrthogonalProjection
