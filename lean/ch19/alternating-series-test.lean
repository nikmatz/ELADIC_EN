-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 19 · Alternating Series Test (Leibniz) · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch19.Enallassousa
open Filter Topology

-- the series b₀ - b₁ + b₂ - …, with b decreasing and b n → 0
theorem leibniz_test (b : ℕ → ℝ) (hb : Antitone b) (hb0 : Tendsto b atTop (𝓝 0)) :
    ∃ S, Tendsto (fun N => ∑ i ∈ Finset.range N, (-1) ^ i * b i) atTop (𝓝 S) ∧
      ∀ N, |S - ∑ i ∈ Finset.range N, (-1) ^ i * b i| ≤ b N := by
  obtain ⟨S, hS⟩ := hb.tendsto_alternating_series_of_tendsto_zero hb0
  refine ⟨S, hS, fun N => ?_⟩
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' N
  · -- N = 2k: S_{2k} ≤ S ≤ S_{2k+1} = S_{2k} + b(2k)
    have h1 := hb.alternating_series_le_tendsto hS k
    have h2 := hb.tendsto_le_alternating_series hS k
    rw [Finset.sum_range_succ, pow_mul, neg_one_sq, one_pow, one_mul] at h2
    rw [abs_le]
    constructor <;> linarith
  · -- N = 2k + 1: S_{2k+2} = S_{2k+1} - b(2k+1) ≤ S ≤ S_{2k+1}
    have h1 := hb.tendsto_le_alternating_series hS k
    have h2 := hb.alternating_series_le_tendsto hS (k + 1)
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, pow_succ, pow_mul,
      neg_one_sq, one_pow, one_mul, neg_one_mul] at h2
    rw [abs_le]
    constructor <;> linarith

end Ch19.Enallassousa
