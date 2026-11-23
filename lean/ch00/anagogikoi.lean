-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 0 · Reduction Formulas · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch0.Anagogikoi
open Real

theorem neg_angle (ω : ℝ) : sin (-ω) = -sin ω ∧ cos (-ω) = cos ω :=
  ⟨sin_neg ω, cos_neg ω⟩

theorem pi_div_two_sub (ω : ℝ) : sin (π / 2 - ω) = cos ω ∧ cos (π / 2 - ω) = sin ω :=
  ⟨sin_pi_div_two_sub ω, cos_pi_div_two_sub ω⟩

theorem pi_div_two_add (ω : ℝ) : sin (π / 2 + ω) = cos ω ∧ cos (π / 2 + ω) = -sin ω := by
  rw [add_comm]
  exact ⟨sin_add_pi_div_two ω, cos_add_pi_div_two ω⟩

theorem pi_sub (ω : ℝ) : sin (π - ω) = sin ω ∧ cos (π - ω) = -cos ω := by
  constructor
  · rw [sin_sub, sin_pi, cos_pi]
    ring
  · rw [cos_sub, sin_pi, cos_pi]
    ring

theorem pi_add (ω : ℝ) : sin (π + ω) = -sin ω ∧ cos (π + ω) = -cos ω := by
  constructor
  · rw [sin_add, sin_pi, cos_pi]
    ring
  · rw [cos_add, sin_pi, cos_pi]
    ring

theorem three_pi_div_two_sub (ω : ℝ) :
    sin (3 * π / 2 - ω) = -cos ω ∧ cos (3 * π / 2 - ω) = -sin ω := by
  have h : 3 * π / 2 - ω = (π / 2 - ω) + π := by ring
  rw [h, sin_add_pi, cos_add_pi, sin_pi_div_two_sub, cos_pi_div_two_sub]
  exact ⟨rfl, rfl⟩

theorem three_pi_div_two_add (ω : ℝ) :
    sin (3 * π / 2 + ω) = -cos ω ∧ cos (3 * π / 2 + ω) = sin ω := by
  have h : 3 * π / 2 + ω = (ω + π / 2) + π := by ring
  rw [h, sin_add_pi, cos_add_pi, sin_add_pi_div_two, cos_add_pi_div_two, neg_neg]
  exact ⟨rfl, rfl⟩

theorem two_pi_sub (ω : ℝ) : sin (2 * π - ω) = -sin ω ∧ cos (2 * π - ω) = cos ω :=
  ⟨sin_two_pi_sub ω, cos_two_pi_sub ω⟩

end Ch0.Anagogikoi
