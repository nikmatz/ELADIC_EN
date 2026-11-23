-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 19 · Absolute Convergence · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch19.ApolytiSygklisi
open Filter Topology

-- the series converges: the partial sums S_N = a₀ + … + a_{N-1} have a limit
theorem abs_conv (a : ℕ → ℝ) (T : ℝ)
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, |a n|) atTop (𝓝 T)) :
    ∃ S, Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop (𝓝 S) := by
  -- the series of the |a n| has nonnegative terms and converges: it is summable
  have hs : Summable (fun n => |a n|) :=
    ((hasSum_iff_tendsto_nat_of_nonneg (fun n => abs_nonneg (a n)) T).mpr h).summable
  -- hence the series of the a n is also summable, and its partial sums converge
  exact ⟨_, (summable_abs_iff.mp hs).hasSum.tendsto_sum_nat⟩

end Ch19.ApolytiSygklisi
