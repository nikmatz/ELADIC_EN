-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 10 · Derivative of the Inverse Function · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch10.AntistrofiParagogos
open Filter Topology

theorem inverse_deriv (f g : ℝ → ℝ) (y₀ f' : ℝ) (hg : ContinuousAt g y₀)
    (hf : HasDerivAt f f' (g y₀)) (hf0 : f' ≠ 0) (hfg : ∀ᶠ y in 𝓝 y₀, f (g y) = y) :
    HasDerivAt g (1 / f') y₀ := by
  rw [one_div]
  exact hf.of_local_left_inverse hg hf0 hfg

theorem arcsin_deriv (x : ℝ) (h : |x| < 1) :
    HasDerivAt Real.arcsin (1 / √(1 - x ^ 2)) x := by
  rw [abs_lt] at h
  exact Real.hasDerivAt_arcsin h.1.ne' h.2.ne

theorem arctan_deriv (x : ℝ) : HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x :=
  Real.hasDerivAt_arctan x

end Ch10.AntistrofiParagogos
