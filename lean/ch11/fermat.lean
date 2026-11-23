-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 11 · Fermat's Theorem · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch11.Fermat
open Filter Topology

theorem fermat_min (f : ℝ → ℝ) (x₀ f' : ℝ) (hmin : IsLocalMin f x₀) (hf : HasDerivAt f f' x₀) :
    f' = 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hf
  have hR : 0 ≤ f' := by
    have h1 : Tendsto (slope f x₀) (𝓝[>] x₀) (𝓝 f') := hf.mono_left (nhdsGT_le_nhdsNE x₀)
    have hm : ∀ᶠ x in 𝓝[>] x₀, f x₀ ≤ f x := nhdsWithin_le_nhds hmin
    apply ge_of_tendsto h1
    filter_upwards [hm, self_mem_nhdsWithin] with x hfx hx
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.mpr hfx) (sub_nonneg.mpr (le_of_lt hx))
  have hL : f' ≤ 0 := by
    have h2 : Tendsto (slope f x₀) (𝓝[<] x₀) (𝓝 f') := hf.mono_left (nhdsLT_le_nhdsNE x₀)
    have hm : ∀ᶠ x in 𝓝[<] x₀, f x₀ ≤ f x := nhdsWithin_le_nhds hmin
    apply le_of_tendsto h2
    filter_upwards [hm, self_mem_nhdsWithin] with x hfx hx
    rw [slope_def_field]
    exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hfx) (sub_nonpos.mpr (le_of_lt hx))
  linarith

theorem fermat_max (f : ℝ → ℝ) (x₀ f' : ℝ) (hmax : IsLocalMax f x₀) (hf : HasDerivAt f f' x₀) :
    f' = 0 := by
  have h := fermat_min (fun x => -f x) x₀ (-f') hmax.neg hf.neg
  linarith

theorem fermat_extr (f : ℝ → ℝ) (x₀ f' : ℝ) (hext : IsLocalExtr f x₀)
    (hf : HasDerivAt f f' x₀) : f' = 0 :=
  hext.hasDerivAt_eq_zero hf

-- a critical point that is not an extremum: f(x) = x³ at 0
theorem cube_critical : HasDerivAt (fun x : ℝ => x ^ 3) 0 0 := by
  simpa using hasDerivAt_pow 3 (0 : ℝ)

theorem cube_not_extr : ¬ IsLocalExtr (fun x : ℝ => x ^ 3) 0 := by
  have hpt : ∀ ε : ℝ, 0 < ε → dist (ε / 2) 0 < ε ∧ dist (-(ε / 2)) 0 < ε := by
    intro ε hε
    rw [Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, abs_neg, abs_of_pos (half_pos hε)]
    constructor <;> linarith
  rintro (h | h)
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
    have h1 : (0 : ℝ) ^ 3 ≤ (-(ε / 2)) ^ 3 := hball (hpt ε hε).2
    have h2 : 0 < (ε / 2) ^ 3 := pow_pos (half_pos hε) 3
    linarith
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
    have h1 : (ε / 2) ^ 3 ≤ (0 : ℝ) ^ 3 := hball (hpt ε hε).1
    have h2 : 0 < (ε / 2) ^ 3 := pow_pos (half_pos hε) 3
    linarith

end Ch11.Fermat
