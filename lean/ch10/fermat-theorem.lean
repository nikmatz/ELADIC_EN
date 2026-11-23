-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 10 · Fermat's Theorem · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch10.Fermat
open Filter Topology

theorem fermat_max (f : ℝ → ℝ) (x₀ f' : ℝ) (hmax : IsLocalMax f x₀) (hf : HasDerivAt f f' x₀) :
    f' = 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hf
  have hR : f' ≤ 0 := by
    have h1 : Tendsto (slope f x₀) (𝓝[>] x₀) (𝓝 f') := hf.mono_left (nhdsGT_le_nhdsNE x₀)
    have hm : ∀ᶠ x in 𝓝[>] x₀, f x ≤ f x₀ := nhdsWithin_le_nhds hmax
    apply le_of_tendsto h1
    filter_upwards [hm, self_mem_nhdsWithin] with x hfx hx
    rw [slope_def_field]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hfx) (sub_nonneg.mpr (le_of_lt hx))
  have hL : 0 ≤ f' := by
    have h2 : Tendsto (slope f x₀) (𝓝[<] x₀) (𝓝 f') := hf.mono_left (nhdsLT_le_nhdsNE x₀)
    have hm : ∀ᶠ x in 𝓝[<] x₀, f x ≤ f x₀ := nhdsWithin_le_nhds hmax
    apply ge_of_tendsto h2
    filter_upwards [hm, self_mem_nhdsWithin] with x hfx hx
    rw [slope_def_field]
    exact div_nonneg_of_nonpos (sub_nonpos.mpr hfx) (sub_nonpos.mpr (le_of_lt hx))
  linarith

theorem fermat_min (f : ℝ → ℝ) (x₀ f' : ℝ) (hmin : IsLocalMin f x₀) (hf : HasDerivAt f f' x₀) :
    f' = 0 := by
  have h := fermat_max (fun x => -f x) x₀ (-f') hmin.neg hf.neg
  linarith

theorem fermat_mathlib (f : ℝ → ℝ) (x₀ f' : ℝ) (hext : IsLocalExtr f x₀)
    (hf : HasDerivAt f f' x₀) : f' = 0 :=
  hext.hasDerivAt_eq_zero hf

end Ch10.Fermat
