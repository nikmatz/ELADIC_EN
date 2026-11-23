-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 0 · Multiplication in Polar Form · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch0.Poliki
open Complex

theorem mul_polar (r₁ r₂ θ₁ θ₂ : ℝ) :
    (r₁ * exp (θ₁ * I)) * (r₂ * exp (θ₂ * I)) = (r₁ * r₂) * exp ((θ₁ + θ₂) * I) := by
  rw [add_mul]
  rw [exp_add]
  ring

theorem div_polar (r₁ r₂ θ₁ θ₂ : ℝ) :
    (r₁ * exp (θ₁ * I)) / (r₂ * exp (θ₂ * I)) = (r₁ / r₂) * exp ((θ₁ - θ₂) * I) := by
  rw [sub_mul]
  rw [exp_sub]
  ring

end Ch0.Poliki
