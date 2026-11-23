-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 11 · Cauchy's Mean Value Theorem (Generalized MVT) · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch11.CauchyMesiTimi

theorem cauchy_mean_value (f f' g g' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.Ioo a b, g' x ≠ 0) :
    ∃ c ∈ Set.Ioo a b, f' c / g' c = (f b - f a) / (g b - g a) := by
  have hgab : g b - g a ≠ 0 := by
    intro h
    obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab hgc (by linarith) hgg'
    exact hg' c hc hc0
  set A := f b - f a with hA
  set B := g b - g a with hB
  have hcont : ContinuousOn (fun x => A * g x - B * f x) (Set.Icc a b) :=
    (continuousOn_const.mul hgc).sub (continuousOn_const.mul hfc)
  have hderiv : ∀ x ∈ Set.Ioo a b,
      HasDerivAt (fun x => A * g x - B * f x) (A * g' x - B * f' x) x := by
    intro x hx
    exact ((hgg' x hx).const_mul A).sub ((hff' x hx).const_mul B)
  have hends : A * g a - B * f a = A * g b - B * f b := by
    rw [hA, hB]
    ring
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab hcont hends hderiv
  refine ⟨c, hc, ?_⟩
  rw [div_eq_div_iff (hg' c hc) hgab]
  linear_combination -hc0

theorem lagrange_from_cauchy (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Set.Ioo a b, f' c = (f b - f a) / (b - a) := by
  obtain ⟨c, hc, h⟩ := cauchy_mean_value f f' (fun x => x) (fun _ => 1) a b hab hfc
    continuousOn_id hff' (fun x _ => hasDerivAt_id' x) (fun _ _ => one_ne_zero)
  exact ⟨c, hc, by simpa using h⟩

-- the Mathlib form, without division
theorem cauchy_mathlib (f f' g g' : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hfc : ContinuousOn f (Set.Icc a b)) (hgc : ContinuousOn g (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Set.Ioo a b, HasDerivAt g (g' x) x) :
    ∃ c ∈ Set.Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c :=
  exists_ratio_hasDerivAt_eq_ratio_slope f f' hab hfc hff' g g' hgc hgg'

end Ch11.CauchyMesiTimi
