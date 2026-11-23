-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 15 · Area by Integration with Respect to y · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch15.EmvadonWsProsY
open MeasureTheory

-- the region: the points (x, y) with y ∈ [c, d] and q(y) < x < p(y)
theorem area_dy (p q : ℝ → ℝ) (c d : ℝ) (hcd : c ≤ d)
    (hp : ContinuousOn p (Set.Icc c d)) (hq : ContinuousOn q (Set.Icc c d))
    (hqp : ∀ y ∈ Set.Icc c d, q y ≤ p y) :
    volume {z : ℝ × ℝ | z.2 ∈ Set.Icc c d ∧ z.1 ∈ Set.Ioo (q z.2) (p z.2)} =
      ENNReal.ofReal (∫ y in c..d, (p y - q y)) := by
  -- swapping the axes (x, y) ↦ (y, x) preserves area
  have hswap : MeasurePreserving (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ)
      (volume.prod volume) (volume.prod volume) := Measure.measurePreserving_swap
  -- after the swap, the region is the region between the graphs of q and p
  have hset : {z : ℝ × ℝ | z.2 ∈ Set.Icc c d ∧ z.1 ∈ Set.Ioo (q z.2) (p z.2)} =
      (MeasurableEquiv.prodComm : ℝ × ℝ ≃ᵐ ℝ × ℝ) ⁻¹' regionBetween q p (Set.Icc c d) := rfl
  rw [Measure.volume_eq_prod, hset, hswap.measure_preimage_equiv,
    volume_regionBetween_eq_integral hq.integrableOn_Icc hp.integrableOn_Icc measurableSet_Icc hqp,
    intervalIntegral.integral_of_le hcd, integral_Icc_eq_integral_Ioc]
  rfl

end Ch15.EmvadonWsProsY
