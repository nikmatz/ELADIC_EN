-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Properties of the Cross Product · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.ExotGinomeno
open Matrix

theorem anticomm (u v : Fin 3 → ℝ) : u ⨯₃ v = -(v ⨯₃ u) := by
  rw [cross_anticomm]

theorem add_left (u w v : Fin 3 → ℝ) : (u + w) ⨯₃ v = u ⨯₃ v + w ⨯₃ v := by
  rw [map_add, LinearMap.add_apply]

theorem smul_left (c : ℝ) (u v : Fin 3 → ℝ) : (c • u) ⨯₃ v = c • (u ⨯₃ v) := by
  rw [map_smul, LinearMap.smul_apply]

theorem perp_left (u v : Fin 3 → ℝ) : u ⬝ᵥ (u ⨯₃ v) = 0 := by
  rw [cross_apply]
  rw [vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  ring

theorem perp_right (u v : Fin 3 → ℝ) : v ⬝ᵥ (u ⨯₃ v) = 0 := by
  rw [cross_apply, vec3_dotProduct]
  dsimp only [Matrix.cons_val]
  ring

theorem lagrange (u v : Fin 3 → ℝ) :
    (u ⨯₃ v) ⬝ᵥ (u ⨯₃ v) = (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 := by
  rw [cross_dot_cross, dotProduct_comm v u]
  ring

theorem zero_iff (u v : Fin 3 → ℝ) : u ⨯₃ v = 0 ↔ ¬ LinearIndependent ℝ ![u, v] := by
  rw [← crossProduct_ne_zero_iff_linearIndependent, not_not]

end Ch1.ExotGinomeno
