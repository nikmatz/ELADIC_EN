-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 19 · Ratio Test (d'Alembert) · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch19.KritirioLogou
open Filter Topology

-- L < 1: the series converges absolutely
theorem ratio_converges (a : ℕ → ℝ) (L : ℝ) (hL : L < 1) (ha : ∀ᶠ n in atTop, a n ≠ 0)
    (h : Tendsto (fun n => |a (n + 1) / a n|) atTop (𝓝 L)) : Summable a := by
  refine summable_of_ratio_test_tendsto_lt_one hL ha ?_
  simpa [Real.norm_eq_abs, abs_div] using h

-- with limsup in place of the limit: |a (n + 1)| ≤ r |a n| for large n, with r < 1
theorem ratio_converges_le (a : ℕ → ℝ) (r : ℝ) (hr : r < 1)
    (h : ∀ᶠ n in atTop, |a (n + 1)| ≤ r * |a n|) : Summable a :=
  summable_of_ratio_norm_eventually_le hr (by simpa [Real.norm_eq_abs] using h)

-- if for large n the ratio is > 1, the partial sums do not converge
theorem diverges_of_ratio (a : ℕ → ℝ) (h : ∀ᶠ n in atTop, 1 < |a (n + 1) / a n|) :
    ¬ ∃ S, Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 S) := by
  rintro ⟨S, hS⟩
  -- necessary condition: a n → 0
  have h0 : Tendsto a atTop (𝓝 0) := by
    have h1 := (hS.comp (tendsto_add_atTop_nat 1)).sub hS
    simp only [Function.comp_def, Finset.sum_range_succ, add_sub_cancel_left, sub_self] at h1
    exact h1
  -- for n ≥ N the ratio is > 1
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hstep : ∀ n ≥ N, a n ≠ 0 ∧ |a n| < |a (n + 1)| := by
    intro n hn
    have h1 := hN n hn
    have ha : a n ≠ 0 := by
      intro h2
      rw [h2, div_zero, abs_zero] at h1
      linarith
    refine ⟨ha, ?_⟩
    rw [abs_div, lt_div_iff₀ (abs_pos.mpr ha), one_mul] at h1
    exact h1
  -- therefore |a n| ≥ |a N| > 0 for every n ≥ N
  have hge : ∀ n ≥ N, |a N| ≤ |a n| := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ k hk ih => exact ih.trans (hstep k hk).2.le
  have hpos : 0 < |a N| := abs_pos.mpr (hstep N le_rfl).1
  -- contradiction with a n → 0
  have h3 := h0.abs.eventually (gt_mem_nhds (show |(0 : ℝ)| < |a N| by
    rw [abs_zero]
    exact hpos))
  obtain ⟨n, hn1, hn2⟩ := (h3.and (eventually_ge_atTop N)).exists
  exact absurd (hge n hn2) (not_le.mpr hn1)

-- L > 1
theorem ratio_diverges (a : ℕ → ℝ) (L : ℝ) (hL : 1 < L)
    (h : Tendsto (fun n => |a (n + 1) / a n|) atTop (𝓝 L)) :
    ¬ ∃ S, Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 S) :=
  diverges_of_ratio a (h.eventually (lt_mem_nhds hL))

-- L = +∞
theorem ratio_diverges_top (a : ℕ → ℝ) (h : Tendsto (fun n => |a (n + 1) / a n|) atTop atTop) :
    ¬ ∃ S, Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 S) :=
  diverges_of_ratio a (h.eventually (eventually_gt_atTop 1))

end Ch19.KritirioLogou
