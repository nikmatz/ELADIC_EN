-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 19 · Necessary Condition for Convergence · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch19.AnagkaiaSynthiki
open Filter Topology

-- if the partial sums S_N converge, then a n → 0
theorem necessary (a : ℕ → ℝ) (S : ℝ)
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 S)) :
    Tendsto a atTop (𝓝 0) := by
  -- the sequence S_{N+1} also tends to S
  have h1 : Tendsto (fun N => ∑ n ∈ Finset.range (N + 1), a n) atTop (𝓝 S) :=
    h.comp (tendsto_add_atTop_nat 1)
  -- a_N = S_{N+1} - S_N
  have h2 : (fun N => ∑ n ∈ Finset.range (N + 1), a n - ∑ n ∈ Finset.range N, a n) = a := by
    funext N
    rw [Finset.sum_range_succ]
    ring
  -- hence a_N → S - S = 0
  have h3 := h1.sub h
  rw [h2, sub_self] at h3
  exact h3

-- the converse does not hold: 1/(n+1) → 0, but the harmonic series diverges
theorem harmonic :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) ∧
      Tendsto (fun N => ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1)) atTop atTop :=
  ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Real.tendsto_sum_range_one_div_nat_succ_atTop⟩

theorem diverges_of_not_tendsto (a : ℕ → ℝ) (h : ¬ Tendsto a atTop (𝓝 0)) :
    ¬ ∃ S, Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 S) := by
  rintro ⟨S, hS⟩
  exact h (necessary a S hS)

end Ch19.AnagkaiaSynthiki
