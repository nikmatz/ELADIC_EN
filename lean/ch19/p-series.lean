-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 19 · p-Series · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch19.PSeira
open Filter Topology

-- the term for n = 0 is 1/0^p, a number that does not affect convergence
theorem p_series (p : ℝ) : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) ↔ 1 < p :=
  Real.summable_one_div_nat_rpow

theorem harmonic_diverges :
    Tendsto (fun N => ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + 1)) atTop atTop :=
  Real.tendsto_sum_range_one_div_nat_succ_atTop

theorem basel : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) :=
  hasSum_zeta_two

theorem half_diverges : ¬ Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 / 2 : ℝ)) := by
  rw [Real.summable_one_div_nat_rpow]
  norm_num

end Ch19.PSeira
