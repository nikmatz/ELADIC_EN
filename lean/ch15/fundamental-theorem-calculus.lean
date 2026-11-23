-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 15 · The Fundamental Theorem of Calculus · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch15.ThemeliodesThewrima
open MeasureTheory

-- Part A: G(x) = ∫ f(t) dt from a to x has derivative f(x) at every x ∈ (a, b)
theorem ftc_part_A (f : ℝ → ℝ) (a b : ℝ) (hf : ContinuousOn f (Set.Icc a b))
    (x : ℝ) (hx : x ∈ Set.Ioo a b) :
    HasDerivAt (fun u => ∫ t in a..u, f t) (f x) x := by
  have hint : IntervalIntegrable f volume a x :=
    (hf.mono (Set.Icc_subset_Icc le_rfl hx.2.le)).intervalIntegrable_of_Icc hx.1.le
  have hmeas : StronglyMeasurableAtFilter f (nhds x) volume :=
    (hf.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas
    (hf.continuousAt (Icc_mem_nhds hx.1 hx.2))

-- Part B (Newton–Leibniz): if F' = f, then the integral of f from a to b is F(b) - F(a)
theorem ftc_part_B (f F : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hF : ContinuousOn F (Set.Icc a b))
    (hFf : ∀ x ∈ Set.Ioo a b, HasDerivAt F (f x) x) (hf : ContinuousOn f (Set.Icc a b)) :
    ∫ x in a..b, f x = F b - F a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF hFf (hf.intervalIntegrable_of_Icc hab)

end Ch15.ThemeliodesThewrima
