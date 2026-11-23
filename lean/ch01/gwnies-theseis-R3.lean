-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Angles and Relative Positions in Space · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.GwniesR3
open scoped InnerProductSpace
open Matrix

theorem plane_angle (n₁ n₂ : EuclideanSpace ℝ (Fin 3)) (h₁ : n₁ ≠ 0) (h₂ : n₂ ≠ 0) :
    0 ≤ |⟪n₁, n₂⟫_ℝ| / (‖n₁‖ * ‖n₂‖) ∧ |⟪n₁, n₂⟫_ℝ| / (‖n₁‖ * ‖n₂‖) ≤ 1 := by
  have hpos : 0 < ‖n₁‖ * ‖n₂‖ := mul_pos (norm_pos_iff.mpr h₁) (norm_pos_iff.mpr h₂)
  constructor
  · exact div_nonneg (abs_nonneg _) hpos.le
  · rw [div_le_one hpos]
    exact abs_real_inner_le_norm n₁ n₂

theorem line_plane_angle (d n : EuclideanSpace ℝ (Fin 3)) (hd : d ≠ 0) (hn : n ≠ 0) :
    0 ≤ |⟪d, n⟫_ℝ| / (‖d‖ * ‖n‖) ∧ |⟪d, n⟫_ℝ| / (‖d‖ * ‖n‖) ≤ 1 := by
  have hpos : 0 < ‖d‖ * ‖n‖ := mul_pos (norm_pos_iff.mpr hd) (norm_pos_iff.mpr hn)
  constructor
  · exact div_nonneg (abs_nonneg _) hpos.le
  · rw [div_le_one hpos]
    exact abs_real_inner_le_norm d n

theorem independent_iff_det (a b c : Fin 3 → ℝ) :
    LinearIndependent ℝ ![a, b, c] ↔ Matrix.det ![a, b, c] ≠ 0 :=
  (Matrix.linearIndependent_row_iff (A := Matrix.of ![a, b, c])).trans
    Matrix.nonsingular_iff_det_ne_zero

theorem coplanar_iff (p₁ p₂ d₁ d₂ : Fin 3 → ℝ) :
    (p₂ - p₁) ⬝ᵥ (d₁ ⨯₃ d₂) = 0 ↔ ¬ LinearIndependent ℝ ![p₂ - p₁, d₁, d₂] := by
  rw [triple_product_eq_det, independent_iff_det, not_not]

end Ch1.GwniesR3
