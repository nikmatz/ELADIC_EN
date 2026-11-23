-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 15 · The Leibniz Rule: Differentiation with Variable Limits · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch15.KanonasLeibniz
open MeasureTheory

theorem leibniz (f a b a' b' : ℝ → ℝ) (hf : Continuous f)
    (ha : ∀ x, HasDerivAt a (a' x) x) (hb : ∀ x, HasDerivAt b (b' x) x) (x : ℝ) :
    HasDerivAt (fun x => ∫ t in a x..b x, f t) (f (b x) * b' x - f (a x) * a' x) x := by
  -- F(u) = ∫ f(t) dt from 0 to u has derivative f(u) (fundamental theorem)
  have hF : ∀ u, HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, f t) (f u) u :=
    fun u => (hf.integral_hasStrictDerivAt 0 u).hasDerivAt
  -- H(x) = F(b(x)) - F(a(x))
  have hH : (fun x => ∫ t in a x..b x, f t) =
      fun x => (∫ t in (0 : ℝ)..b x, f t) - ∫ t in (0 : ℝ)..a x, f t := by
    funext y
    rw [intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable (μ := volume) 0 (b y))
      (hf.intervalIntegrable (μ := volume) 0 (a y))]
  rw [hH]
  -- chain rule for each of the two integrals
  have h1 := (hF (b x)).comp x (hb x)
  have h2 := (hF (a x)).comp x (ha x)
  exact h1.sub h2

theorem leibniz_square (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    HasDerivAt (fun x => ∫ t in (0 : ℝ)..x ^ 2, f t) (f (x ^ 2) * (2 * x)) x := by
  have h := leibniz f (fun _ => 0) (fun x => x ^ 2) (fun _ => 0) (fun x => 2 * x) hf
    (fun x => hasDerivAt_const x 0) (fun x => by simpa using hasDerivAt_pow 2 x) x
  simp only [mul_zero, sub_zero] at h
  exact h

end Ch15.KanonasLeibniz
