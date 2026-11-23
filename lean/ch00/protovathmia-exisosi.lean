-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 0 · Solution of a First-Degree Equation · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch0.Exisosi

theorem is_solution (a b : ℝ) (ha : a ≠ 0) : a * (-b / a) + b = 0 := by
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ ha]
  ring

theorem unique (a b x : ℝ) (ha : a ≠ 0) (hx : a * x + b = 0) : x = -b / a := by
  rw [eq_div_iff ha]
  linarith

theorem exists_unique (a b : ℝ) (ha : a ≠ 0) : ∃! x : ℝ, a * x + b = 0 :=
  ⟨-b / a, is_solution a b ha, fun x hx => unique a b x ha hx⟩

end Ch0.Exisosi
