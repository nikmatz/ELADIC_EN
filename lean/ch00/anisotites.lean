-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 0 · Properties of Inequalities · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch0.Anisotites

theorem add_c (a b c : ℝ) (h : a < b) : a + c < b + c :=
  add_lt_add_left h c

theorem mul_c_pos (a b c : ℝ) (h : a < b) (hc : 0 < c) : a * c < b * c :=
  mul_lt_mul_of_pos_right h hc

theorem mul_c_neg (a b c : ℝ) (h : a < b) (hc : c < 0) : a * c > b * c :=
  mul_lt_mul_of_neg_right h hc

theorem transitivity (a b c : ℝ) (h₁ : a < b) (h₂ : b < c) : a < c :=
  lt_trans h₁ h₂

theorem inverse (a b : ℝ) (ha : 0 < a) (hab : a < b) : 1 / a > 1 / b := by
  have hb : 0 < b := lt_trans ha hab
  have key : 1 / a - 1 / b = (b - a) / (a * b) := by
    rw [div_sub_div _ _ ha.ne' hb.ne']
    ring
  have pos : 0 < (b - a) / (a * b) := div_pos (sub_pos.mpr hab) (mul_pos ha hb)
  linarith

end Ch0.Anisotites
