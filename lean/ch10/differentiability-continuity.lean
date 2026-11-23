-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 10 · Differentiability ⇒ Continuity · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch10.ParagogisimotitaSynexeia
open Filter Topology

theorem continuous_of_hasDeriv (f : ℝ → ℝ) (x₀ f' : ℝ) (hf : HasDerivAt f f' x₀) :
    ContinuousAt f x₀ := by
  rw [hasDerivAt_iff_tendsto_slope] at hf
  have h1 : Tendsto (fun x => x - x₀) (𝓝[≠] x₀) (𝓝 0) := by
    have h : Tendsto (fun x => x - x₀) (𝓝 x₀) (𝓝 (x₀ - x₀)) :=
      (continuous_id.sub continuous_const).tendsto x₀
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun x => slope f x₀ x * (x - x₀)) (𝓝[≠] x₀) (𝓝 (f' * 0)) := hf.mul h1
  rw [mul_zero] at h2
  have h3 : Tendsto (fun x => f x - f x₀) (𝓝[≠] x₀) (𝓝 0) := by
    apply h2.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [slope_def_field, div_mul_cancel₀ _ (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hx))]
  rw [continuousAt_iff_punctured_nhds]
  have h4 := h3.add_const (f x₀)
  simpa using h4

theorem sum_continuous (f g : ℝ → ℝ) (x₀ f' g' : ℝ) (hf : HasDerivAt f f' x₀)
    (hg : HasDerivAt g g' x₀) : ContinuousAt (fun x => f x + g x) x₀ :=
  continuous_of_hasDeriv _ x₀ (f' + g') (hf.add hg)

theorem abs_counterexample :
    ContinuousAt (fun x : ℝ => |x|) 0 ∧ ¬ DifferentiableAt ℝ (fun x : ℝ => |x|) 0 :=
  ⟨continuous_abs.continuousAt, not_differentiableAt_abs_zero⟩

end Ch10.ParagogisimotitaSynexeia
