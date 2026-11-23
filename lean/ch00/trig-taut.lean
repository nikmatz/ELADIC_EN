-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 0 · Fundamental Trigonometric Identities · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch0.TrigTautotites
open Real

theorem pythagorean (θ : ℝ) : sin θ ^ 2 + cos θ ^ 2 = 1 := sin_sq_add_cos_sq θ

theorem one_add_tan_sq (θ : ℝ) (h : cos θ ≠ 0) : 1 + tan θ ^ 2 = 1 / cos θ ^ 2 := by
  have h2 : cos θ ^ 2 ≠ 0 := pow_ne_zero 2 h
  rw [tan_eq_sin_div_cos, div_pow, eq_div_iff h2, add_mul, one_mul, div_mul_cancel₀ _ h2]
  linarith [sin_sq_add_cos_sq θ]

theorem sin_of_sum (α β : ℝ) : sin (α + β) = sin α * cos β + cos α * sin β := sin_add α β

theorem sin_of_diff (α β : ℝ) : sin (α - β) = sin α * cos β - cos α * sin β := sin_sub α β

theorem cos_of_sum (α β : ℝ) : cos (α + β) = cos α * cos β - sin α * sin β := cos_add α β

theorem cos_of_diff (α β : ℝ) : cos (α - β) = cos α * cos β + sin α * sin β := cos_sub α β

theorem sin_double (α : ℝ) : sin (2 * α) = 2 * sin α * cos α := sin_two_mul α

theorem cos_double (α : ℝ) : cos (2 * α) = cos α ^ 2 - sin α ^ 2 := by
  rw [cos_two_mul]
  linear_combination sin_sq_add_cos_sq α

end Ch0.TrigTautotites
