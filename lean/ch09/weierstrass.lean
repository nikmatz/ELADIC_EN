-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 9 · Weierstrass' Theorem · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch9.Weierstrass

theorem extreme_values (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ xmin ∈ Set.Icc a b, ∃ xmax ∈ Set.Icc a b,
      ∀ x ∈ Set.Icc a b, f xmin ≤ f x ∧ f x ≤ f xmax := by
  obtain ⟨xmin, hmin, hmin'⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hab) hf
  obtain ⟨xmax, hmax, hmax'⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hf
  exact ⟨xmin, hmin, xmax, hmax, fun x hx => ⟨isMinOn_iff.mp hmin' x hx, isMaxOn_iff.mp hmax' x hx⟩⟩

end Ch9.Weierstrass
