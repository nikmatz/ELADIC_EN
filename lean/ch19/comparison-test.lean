-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 19 · Comparison Test · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch19.KritirioSygkrisis

theorem comparison (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hab : ∀ n, a n ≤ b n)
    (hb : Summable b) : Summable a := by
  -- the partial sums of a are bounded by the sum of b
  have hbound : ∀ N, ∑ n ∈ Finset.range N, a n ≤ ∑' n, b n := by
    intro N
    -- term by term: a n ≤ b n
    have h1 : ∑ n ∈ Finset.range N, a n ≤ ∑ n ∈ Finset.range N, b n :=
      Finset.sum_le_sum fun n _ => hab n
    -- every partial sum of b is ≤ the sum of the series, because b n ≥ 0
    have h2 : ∑ n ∈ Finset.range N, b n ≤ ∑' n, b n :=
      hb.sum_le_tsum (Finset.range N) fun n _ => (ha n).trans (hab n)
    exact h1.trans h2
  -- nonnegative terms with bounded partial sums: the series converges
  exact summable_of_sum_range_le ha hbound

-- the same, when 0 ≤ a n ≤ b n holds only for n ≥ N
theorem comparison_from (a b : ℕ → ℝ) (N : ℕ) (ha : ∀ n ≥ N, 0 ≤ a n)
    (hab : ∀ n ≥ N, a n ≤ b n) (hb : Summable b) : Summable a := by
  -- we apply the test to the tails a (n + N) and b (n + N)
  have h := comparison (fun n => a (n + N)) (fun n => b (n + N))
    (fun n => ha (n + N) (Nat.le_add_left N n)) (fun n => hab (n + N) (Nat.le_add_left N n))
    ((summable_nat_add_iff N).mpr hb)
  exact (summable_nat_add_iff N).mp h

theorem comparison_diverges (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hab : ∀ n, a n ≤ b n)
    (hdiv : ¬ Summable a) : ¬ Summable b :=
  fun hb => hdiv (comparison a b ha hab hb)

end Ch19.KritirioSygkrisis
