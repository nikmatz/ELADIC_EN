-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 11 · The Mean Value Theorem (MVT) · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch11.MesiTimi

theorem mean_value (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hfc : ContinuousOn f (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a) := by
  set k := (f b - f a) / (b - a) with hk
  -- g(x) = f(x) - (f(a) + k (x - a)): the vertical distance from the chord
  have hcont : ContinuousOn (fun x => f x - (f a + k * (x - a))) (Set.Icc a b) :=
    hfc.sub (continuousOn_const.add (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
  have hderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun x => f x - (f a + k * (x - a))) (f' x - k) x := by
    intro x hx
    have h := (((hasDerivAt_id x).sub_const a).const_mul k).const_add (f a)
    rw [mul_one] at h
    exact (hff' x hx).sub h
  have hends : f a - (f a + k * (a - a)) = f b - (f a + k * (b - a)) := by
    rw [hk, div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]
    ring
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab hcont hends hderiv
  exact ⟨c, hc, by linarith⟩

theorem zero_deriv_const (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (h0 : ∀ x ∈ Set.Ioo a b, f' x = 0) : f b = f a := by
  obtain ⟨c, hc, h⟩ := mean_value f f' a b hab hfc hff'
  rw [h0 c hc, eq_comm, div_eq_zero_iff, sub_eq_zero, sub_eq_zero] at h
  rcases h with h | h
  · exact h
  · exact absurd h hab.ne'

end Ch11.MesiTimi
