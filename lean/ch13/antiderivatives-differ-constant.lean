-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 13 · Antiderivatives Differ by a Constant · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch13.AntiparagogoiStathera

theorem antiderivatives_differ_const (F G f : ℝ → ℝ) (a b : ℝ)
    (hF : ∀ x ∈ Set.Ioo a b, HasDerivAt F (f x) x) (hG : ∀ x ∈ Set.Ioo a b, HasDerivAt G (f x) x) :
    ∃ C, ∀ x ∈ Set.Ioo a b, G x = F x + C := by
  -- the difference H = G - F has derivative 0
  have hH : ∀ x ∈ Set.Ioo a b, HasDerivAt (fun x => G x - F x) 0 x := by
    intro x hx
    have h := (hG x hx).sub (hF x hx)
    rw [sub_self] at h
    exact h
  -- mean value theorem: H takes the same value at any two points
  have hconst : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, x < y → G y - F y = G x - F x := by
    intro x hx y hy hxy
    have hcont : ContinuousOn (fun x => G x - F x) (Set.Icc x y) := fun z hz =>
      (hH z ⟨hx.1.trans_le hz.1, hz.2.trans_lt hy.2⟩).continuousAt.continuousWithinAt
    obtain ⟨c, -, hc⟩ := exists_hasDerivAt_eq_slope (fun x => G x - F x) (fun _ => 0) hxy hcont
      (fun z hz => hH z ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩)
    have h : (G y - F y - (G x - F x)) / (y - x) = 0 := hc.symm
    rw [div_eq_zero_iff, sub_eq_zero] at h
    exact h.resolve_right (sub_ne_zero.mpr hxy.ne')
  by_cases hab : a < b
  · have hm : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
    refine ⟨G ((a + b) / 2) - F ((a + b) / 2), fun x hx => ?_⟩
    rcases lt_trichotomy x ((a + b) / 2) with h | h | h
    · have := hconst x hx _ hm h
      linarith
    · rw [h]
      ring
    · have := hconst _ hm x hx h
      linarith
  · exact ⟨0, fun x hx => absurd (hx.1.trans hx.2) hab⟩

theorem same_value_same_function (F G f : ℝ → ℝ) (a b x₀ : ℝ) (hx₀ : x₀ ∈ Set.Ioo a b)
    (hF : ∀ x ∈ Set.Ioo a b, HasDerivAt F (f x) x) (hG : ∀ x ∈ Set.Ioo a b, HasDerivAt G (f x) x)
    (h0 : G x₀ = F x₀) : ∀ x ∈ Set.Ioo a b, G x = F x := by
  obtain ⟨C, hC⟩ := antiderivatives_differ_const F G f a b hF hG
  have hC0 : C = 0 := by
    have h := hC x₀ hx₀
    linarith
  intro x hx
  rw [hC x hx, hC0, add_zero]

end Ch13.AntiparagogoiStathera
