-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 11 · First Derivative Test for Extrema · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch11.KritirioProtisParagogou

theorem first_derivative_test_max (f f' : ℝ → ℝ) (a b x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo a b)
    (hc : ContinuousOn f (Set.Icc a b)) (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Set.Ioo a x₀, 0 < f' x) (hneg : ∀ x ∈ Set.Ioo x₀ b, f' x < 0) :
    IsLocalMax f x₀ := by
  filter_upwards [Ioo_mem_nhds hx₀.1 hx₀.2] with x hx
  rcases lt_trichotomy x x₀ with hlt | heq | hgt
  · obtain ⟨c, hc', hfc⟩ := exists_hasDerivAt_eq_slope f f' hlt
      (hc.mono (Set.Icc_subset_Icc hx.1.le hx₀.2.le))
      (fun y hy => hd y ⟨hx.1.trans hy.1, hy.2.trans hx₀.2⟩)
    have h1 : 0 < f' c := hpos c ⟨hx.1.trans hc'.1, hc'.2⟩
    rw [hfc, lt_div_iff₀ (sub_pos.mpr hlt)] at h1
    linarith
  · rw [heq]
  · obtain ⟨c, hc', hfc⟩ := exists_hasDerivAt_eq_slope f f' hgt
      (hc.mono (Set.Icc_subset_Icc hx₀.1.le hx.2.le))
      (fun y hy => hd y ⟨hx₀.1.trans hy.1, hy.2.trans hx.2⟩)
    have h1 : f' c < 0 := hneg c ⟨hc'.1, hc'.2.trans hx.2⟩
    rw [hfc, div_lt_iff₀ (sub_pos.mpr hgt)] at h1
    linarith

theorem first_derivative_test_min (f f' : ℝ → ℝ) (a b x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo a b)
    (hc : ContinuousOn f (Set.Icc a b)) (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hneg : ∀ x ∈ Set.Ioo a x₀, f' x < 0) (hpos : ∀ x ∈ Set.Ioo x₀ b, 0 < f' x) :
    IsLocalMin f x₀ := by
  have h := first_derivative_test_max (fun x => -f x) (fun x => -f' x) a b x₀ hx₀ hc.neg
    (fun x hx => (hd x hx).neg) (fun x hx => neg_pos.mpr (hneg x hx))
    (fun x hx => neg_lt_zero.mpr (hpos x hx))
  simpa using h.neg

end Ch11.KritirioProtisParagogou
