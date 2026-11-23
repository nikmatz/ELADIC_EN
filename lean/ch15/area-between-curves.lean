-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 15 · Area of the Region between Two Curves · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch15.EmvadonDyoKampylon
open MeasureTheory

-- the region: the points (x, y) with x ∈ [α, β] and g(x) < y < f(x)
theorem area_between (f g : ℝ → ℝ) (α β : ℝ) (hαβ : α ≤ β)
    (hf : ContinuousOn f (Set.Icc α β)) (hg : ContinuousOn g (Set.Icc α β))
    (hgf : ∀ x ∈ Set.Icc α β, g x ≤ f x) :
    volume (regionBetween g f (Set.Icc α β)) = ENNReal.ofReal (∫ x in α..β, (f x - g x)) := by
  rw [Measure.volume_eq_prod, volume_regionBetween_eq_integral hg.integrableOn_Icc
    hf.integrableOn_Icc measurableSet_Icc hgf, intervalIntegral.integral_of_le hαβ,
    integral_Icc_eq_integral_Ioc]
  rfl

end Ch15.EmvadonDyoKampylon
