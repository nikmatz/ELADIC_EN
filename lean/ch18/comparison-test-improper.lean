-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 18 · The Comparison Test for Improper Integrals · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch18.KritirioSygkrisis
open MeasureTheory Filter Topology

-- for nonnegative f, “the integral from a to +∞ converges” is written IntegrableOn f (Set.Ioi a)
theorem comparison (f g : ℝ → ℝ) (a : ℝ) (hf : ContinuousOn f (Set.Ici a))
    (hf0 : ∀ x ∈ Set.Ici a, 0 ≤ f x) (hfg : ∀ x ∈ Set.Ici a, f x ≤ g x)
    (hg : IntegrableOn g (Set.Ioi a)) : IntegrableOn f (Set.Ioi a) := by
  refine Integrable.mono' hg ((hf.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x (Set.Ioi_subset_Ici_self hx))]
  exact hfg x (Set.Ioi_subset_Ici_self hx)

theorem comparison_diverges (f g : ℝ → ℝ) (a : ℝ) (hf : ContinuousOn f (Set.Ici a))
    (hf0 : ∀ x ∈ Set.Ici a, 0 ≤ f x) (hfg : ∀ x ∈ Set.Ici a, f x ≤ g x)
    (hdiv : ¬ IntegrableOn f (Set.Ioi a)) : ¬ IntegrableOn g (Set.Ioi a) :=
  fun hg => hdiv (comparison f g a hf hf0 hfg hg)

-- connection with the definition in the book (1): then the integral from a to R has a limit as R → +∞
theorem limit_of_integrable (f : ℝ → ℝ) (a : ℝ) (hf : IntegrableOn f (Set.Ioi a)) :
    Tendsto (fun R => ∫ x in a..R, f x) atTop (𝓝 (∫ x in Set.Ioi a, f x)) :=
  intervalIntegral_tendsto_integral_Ioi a hf tendsto_id

-- connection with the definition in the book (2): for nonnegative f the converse also holds
theorem integrable_of_limit (f : ℝ → ℝ) (a L : ℝ) (hf : ContinuousOn f (Set.Ici a))
    (hf0 : ∀ x ∈ Set.Ici a, 0 ≤ f x)
    (hlim : Tendsto (fun R => ∫ x in a..R, f x) atTop (𝓝 L)) : IntegrableOn f (Set.Ioi a) := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto L a (fun R => ?_) tendsto_id ?_
  · exact ((hf.mono Set.Icc_subset_Ici_self).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · refine hlim.congr' ((eventually_ge_atTop a).mono fun R hR => ?_)
    show ∫ x in a..R, f x = ∫ x in a..R, ‖f x‖
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hR] at hx
    simp only [Real.norm_eq_abs, abs_of_nonneg (hf0 x hx.1)]

end Ch18.KritirioSygkrisis
