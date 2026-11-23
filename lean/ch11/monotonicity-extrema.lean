-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 11 · Monotonicity and Extrema · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch11.MonotoniaAkrotata

theorem strict_mono_of_deriv_pos (f f' : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) (hpos : ∀ x ∈ Set.Ioo a b, 0 < f' x) :
    StrictMonoOn f (Set.Ioo a b) := by
  intro x hx y hy hxy
  have hcont : ContinuousOn f (Set.Icc x y) := by
    intro z hz
    exact (hd z ⟨hx.1.trans_le hz.1, hz.2.trans_lt hy.2⟩).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hfc⟩ := exists_hasDerivAt_eq_slope f f' hxy hcont
    (fun z hz => hd z ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩)
  have h1 : 0 < f' c := hpos c ⟨hx.1.trans hc.1, hc.2.trans hy.2⟩
  rw [hfc, lt_div_iff₀ (sub_pos.mpr hxy)] at h1
  linarith

theorem strict_anti_of_deriv_neg (f f' : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) (hneg : ∀ x ∈ Set.Ioo a b, f' x < 0) :
    StrictAntiOn f (Set.Ioo a b) := by
  have h := strict_mono_of_deriv_pos (fun x => -f x) (fun x => -f' x) a b
    (fun x hx => (hd x hx).neg) (fun x hx => neg_pos.mpr (hneg x hx))
  intro x hx y hy hxy
  exact neg_lt_neg_iff.mp (h hx hy hxy)

-- sign change of f' around x₀: local extremum (theorems from Mathlib)
theorem local_max_of_sign_change (f : ℝ → ℝ) (a b x₀ : ℝ) (ha : a < x₀) (hb : x₀ < b)
    (hc : ContinuousAt f x₀) (hd₀ : DifferentiableOn ℝ f (Set.Ioo a x₀))
    (hd₁ : DifferentiableOn ℝ f (Set.Ioo x₀ b))
    (hpos : ∀ x ∈ Set.Ioo a x₀, 0 ≤ deriv f x) (hneg : ∀ x ∈ Set.Ioo x₀ b, deriv f x ≤ 0) :
    IsLocalMax f x₀ :=
  isLocalMax_of_deriv_Ioo ha hb hc hd₀ hd₁ hpos hneg

theorem local_min_of_sign_change (f : ℝ → ℝ) (a b x₀ : ℝ) (ha : a < x₀) (hb : x₀ < b)
    (hc : ContinuousAt f x₀) (hd₀ : DifferentiableOn ℝ f (Set.Ioo a x₀))
    (hd₁ : DifferentiableOn ℝ f (Set.Ioo x₀ b))
    (hneg : ∀ x ∈ Set.Ioo a x₀, deriv f x ≤ 0) (hpos : ∀ x ∈ Set.Ioo x₀ b, 0 ≤ deriv f x) :
    IsLocalMin f x₀ :=
  isLocalMin_of_deriv_Ioo ha hb hc hd₀ hd₁ hneg hpos

end Ch11.MonotoniaAkrotata
