-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Properties of the Inner Product · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.EsotGinomeno
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem symmetric (u v : V) : ⟪u, v⟫_ℝ = ⟪v, u⟫_ℝ := real_inner_comm v u

theorem add_left (u v w : V) : ⟪u + v, w⟫_ℝ = ⟪u, w⟫_ℝ + ⟪v, w⟫_ℝ := inner_add_left u v w

theorem smul_left (c : ℝ) (u v : V) : ⟪c • u, v⟫_ℝ = c * ⟪u, v⟫_ℝ := real_inner_smul_left u v c

theorem add_right (u v w : V) : ⟪u, v + w⟫_ℝ = ⟪u, v⟫_ℝ + ⟪u, w⟫_ℝ := inner_add_right u v w

theorem smul_right (c : ℝ) (u v : V) : ⟪u, c • v⟫_ℝ = c * ⟪u, v⟫_ℝ := real_inner_smul_right u v c

theorem nonneg (u : V) : 0 ≤ ⟪u, u⟫_ℝ := real_inner_self_nonneg

theorem zero_iff (u : V) : ⟪u, u⟫_ℝ = 0 ↔ u = 0 := inner_self_eq_zero

end Ch1.EsotGinomeno
