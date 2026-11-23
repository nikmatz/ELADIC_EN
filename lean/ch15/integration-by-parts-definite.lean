-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 15 · Integration by Parts in a Definite Integral · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch15.KataParagontesOrismeno
open MeasureTheory

theorem parts_definite (u v u' v' : ℝ → ℝ) (a b : ℝ)
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x) (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x)
    (hu' : ContinuousOn u' (Set.uIcc a b)) (hv' : ContinuousOn v' (Set.uIcc a b)) :
    ∫ x in a..b, u x * v' x = (u b * v b - u a * v a) - ∫ x in a..b, u' x * v x := by
  -- product rule: (u v)' = u' v + u v'
  have hd : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun x => u x * v x) (u' x * v x + u x * v' x) x :=
    fun x hx => (hu x hx).mul (hv x hx)
  -- u, v are continuous, so u' v and u v' are integrable
  have huc : ContinuousOn u (Set.uIcc a b) := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hvc : ContinuousOn v (Set.uIcc a b) := fun x hx => (hv x hx).continuousAt.continuousWithinAt
  have h1 : IntervalIntegrable (fun x => u' x * v x) volume a b := (hu'.mul hvc).intervalIntegrable
  have h2 : IntervalIntegrable (fun x => u x * v' x) volume a b := (huc.mul hv').intervalIntegrable
  -- fundamental theorem for u v
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (h1.add h2)
  -- the integral of the sum splits into two integrals
  rw [intervalIntegral.integral_add h1 h2] at hftc
  linarith

theorem parts_zero_boundary (u v u' v' : ℝ → ℝ) (a b : ℝ)
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x) (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x)
    (hu' : ContinuousOn u' (Set.uIcc a b)) (hv' : ContinuousOn v' (Set.uIcc a b))
    (ha : u a * v a = 0) (hb : u b * v b = 0) :
    ∫ x in a..b, u x * v' x = -∫ x in a..b, u' x * v x := by
  rw [parts_definite u v u' v' a b hu hv hu' hv', ha, hb]
  ring

end Ch15.KataParagontesOrismeno
