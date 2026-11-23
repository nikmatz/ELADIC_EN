-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 15 · Substitution in a Definite Integral (Change of Limits) · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch15.AntikatastasiOrismeno
open MeasureTheory

theorem subst_definite (f g g' : ℝ → ℝ) (a b : ℝ) (hf : Continuous f)
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x) (hg' : ContinuousOn g' (Set.uIcc a b)) :
    ∫ x in a..b, f (g x) * g' x = ∫ u in g a..g b, f u := by
  -- F(u) = ∫ f(t) dt from g(a) to u has derivative f(u)
  have hF : ∀ u, HasDerivAt (fun u => ∫ t in g a..u, f t) (f u) u :=
    fun u => (hf.integral_hasStrictDerivAt (g a) u).hasDerivAt
  -- chain rule: (F(g(x)))' = f(g(x)) g'(x)
  have hcomp : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x => ∫ t in g a..g x, f t) (f (g x) * g' x) x :=
    fun x hx => (hF (g x)).comp x (hg x hx)
  -- f(g(x)) g'(x) is continuous, hence integrable
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun x => f (g x) * g' x) volume a b :=
    ((hf.comp_continuousOn hgc).mul hg').intervalIntegrable
  -- fundamental theorem: the integral is F(g(b)) - F(g(a))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hcomp hint]
  -- F(g(a)) = 0, because the limits are equal
  rw [intervalIntegral.integral_same, sub_zero]

theorem shift (f : ℝ → ℝ) (a b c : ℝ) (hf : Continuous f) :
    ∫ x in a..b, f (x + c) = ∫ u in a + c..b + c, f u := by
  have h := subst_definite f (fun x => x + c) (fun _ => 1) a b hf
    (fun x _ => (hasDerivAt_id' x).add_const c) continuousOn_const
  simp only [mul_one] at h
  exact h

end Ch15.AntikatastasiOrismeno
