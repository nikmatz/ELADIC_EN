-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 19 · Geometric Series — Convergence and Sum · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch19.GewmetrikiSeira
open Filter Topology

-- partial sums: a + a r + … + a r^N = a (1 - r^(N+1))/(1 - r)
theorem partial_sum (a r : ℝ) (hr : r ≠ 1) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), a * r ^ n = a * (1 - r ^ (N + 1)) / (1 - r) := by
  rw [← Finset.mul_sum, geom_sum_eq hr (N + 1)]
  have h1 : r - 1 ≠ 0 := sub_ne_zero.mpr hr
  have h2 : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  field_simp
  ring

-- for |r| < 1 the partial sums tend to a/(1 - r)
theorem geometric_sum (a r : ℝ) (hr : |r| < 1) :
    Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), a * r ^ n) atTop (𝓝 (a / (1 - r))) := by
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, abs_one] at hr
    exact lt_irrefl 1 hr
  have h1 : (fun N => ∑ n ∈ Finset.range (N + 1), a * r ^ n) =
      fun N => a * (1 - r ^ (N + 1)) / (1 - r) := by
    funext N
    exact partial_sum a r hr1 N
  rw [h1]
  have h2 : Tendsto (fun N : ℕ => r ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).comp (tendsto_add_atTop_nat 1)
  have h3 : Tendsto (fun N : ℕ => a * (1 - r ^ (N + 1)) / (1 - r)) atTop
      (𝓝 (a * (1 - 0) / (1 - r))) :=
    ((tendsto_const_nhds.sub h2).const_mul a).div_const (1 - r)
  rw [sub_zero, mul_one] at h3
  exact h3

-- for |r| ≥ 1 (and a ≠ 0) the series diverges
theorem geometric_diverges (a r : ℝ) (ha : a ≠ 0) (hr : 1 ≤ |r|) :
    ¬ ∃ S, Tendsto (fun N => ∑ n ∈ Finset.range N, a * r ^ n) atTop (𝓝 S) := by
  rintro ⟨S, hS⟩
  -- the terms would tend to 0
  have h0 : Tendsto (fun n => a * r ^ n) atTop (𝓝 0) := by
    have h1 := (hS.comp (tendsto_add_atTop_nat 1)).sub hS
    simp only [Function.comp_def, Finset.sum_range_succ, add_sub_cancel_left, sub_self] at h1
    exact h1
  -- but |a rⁿ| ≥ |a| > 0
  have h2 : ∀ n : ℕ, |a| ≤ |a * r ^ n| := fun n => by
    rw [abs_mul, abs_pow]
    exact le_mul_of_one_le_right (abs_nonneg a) (one_le_pow₀ hr)
  have h3 := h0.abs.eventually (gt_mem_nhds (show |(0 : ℝ)| < |a| by
    rw [abs_zero]
    exact abs_pos.mpr ha))
  obtain ⟨n, hn⟩ := h3.exists
  exact absurd (h2 n) (not_le.mpr hn)

theorem half_series :
    Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ n) atTop (𝓝 2) := by
  have h := geometric_sum 1 (1 / 2) (by rw [abs_of_pos (by norm_num)]; norm_num)
  simp only [one_mul] at h
  rwa [show (1 : ℝ) / (1 - 1 / 2) = 2 by norm_num] at h

end Ch19.GewmetrikiSeira
