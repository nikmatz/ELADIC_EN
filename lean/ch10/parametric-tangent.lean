-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 10 · Slope of the Tangent Line to a Parametric Curve · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch10.Parametriki
open Filter Topology

theorem slope_parametric (x y F : ℝ → ℝ) (t₀ x' y' F' : ℝ) (hx : HasDerivAt x x' t₀)
    (hy : HasDerivAt y y' t₀) (hF : HasDerivAt F F' (x t₀))
    (hcurve : ∀ᶠ t in 𝓝 t₀, y t = F (x t)) (hx0 : x' ≠ 0) : F' = y' / x' := by
  have h1 : HasDerivAt (F ∘ x) (F' * x') t₀ := hF.comp t₀ hx
  have h2 : HasDerivAt y (F' * x') t₀ := h1.congr_of_eventuallyEq hcurve
  have h3 : y' = F' * x' := hy.unique h2
  rw [h3, mul_div_cancel_right₀ _ hx0]

theorem horizontal_iff (x' y' : ℝ) (hx0 : x' ≠ 0) : y' / x' = 0 ↔ y' = 0 := by
  rw [div_eq_zero_iff, or_iff_left hx0]

-- vertical tangent line: the curve is written x = G(y) and dx/dy = 0
theorem vertical_tangent (x y G : ℝ → ℝ) (t₀ x' y' G' : ℝ) (hx : HasDerivAt x x' t₀)
    (hy : HasDerivAt y y' t₀) (hG : HasDerivAt G G' (y t₀))
    (hcurve : ∀ᶠ t in 𝓝 t₀, x t = G (y t)) (hy0 : y' ≠ 0) (hx0 : x' = 0) : G' = 0 := by
  rw [slope_parametric y x G t₀ y' x' G' hy hx hG hcurve hy0, hx0, zero_div]

-- second derivative: F' is dy/dx as a function of x, and F'' is d²y/dx²
theorem second_derivative (x F' : ℝ → ℝ) (t₀ x' F'' d : ℝ) (hx : HasDerivAt x x' t₀)
    (hF' : HasDerivAt F' F'' (x t₀)) (hd : HasDerivAt (fun t => F' (x t)) d t₀)
    (hx0 : x' ≠ 0) : F'' = d / x' :=
  slope_parametric x (fun t => F' (x t)) F' t₀ x' d F'' hx hd hF'
    (Eventually.of_forall fun _ => rfl) hx0

end Ch10.Parametriki
