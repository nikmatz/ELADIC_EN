-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 20 · Truncation Error Estimate — Alternating Series · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch20.SfalmaEnallassousas
open Filter Topology

-- I = b₀ - b₁ + b₂ - …, and I_N = Σ from n = 0 to N of (-1)ⁿ bₙ, that is, N + 1 terms
theorem alternating_error (b : ℕ → ℝ) (hb : Antitone b) (hb0 : Tendsto b atTop (𝓝 0)) :
    ∃ I, Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), (-1) ^ n * b n) atTop (𝓝 I) ∧
      ∀ N, |I - ∑ n ∈ Finset.range (N + 1), (-1) ^ n * b n| ≤ b (N + 1) := by
  obtain ⟨I, hI⟩ := hb.tendsto_alternating_series_of_tendsto_zero hb0
  -- the bound |I - S_M| ≤ b M for the sum S_M of the first M terms
  have key : ∀ M, |I - ∑ n ∈ Finset.range M, (-1) ^ n * b n| ≤ b M := by
    intro M
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' M
    · -- M = 2k: S_{2k} ≤ I ≤ S_{2k+1} = S_{2k} + b(2k)
      have h1 := hb.alternating_series_le_tendsto hI k
      have h2 := hb.tendsto_le_alternating_series hI k
      rw [Finset.sum_range_succ, pow_mul, neg_one_sq, one_pow, one_mul] at h2
      rw [abs_le]
      constructor <;> linarith
    · -- M = 2k + 1: S_{2k+2} = S_{2k+1} - b(2k+1) ≤ I ≤ S_{2k+1}
      have h1 := hb.tendsto_le_alternating_series hI k
      have h2 := hb.alternating_series_le_tendsto hI (k + 1)
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ, pow_succ, pow_mul,
        neg_one_sq, one_pow, one_mul, neg_one_mul] at h2
      rw [abs_le]
      constructor <;> linarith
  -- with M = N + 1 terms we get the bound b(N + 1)
  exact ⟨I, hI.comp (tendsto_add_atTop_nat 1), fun N => key (N + 1)⟩

end Ch20.SfalmaEnallassousas
