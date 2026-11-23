-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 19 · Cauchy Criterion for Sequences · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch19.KritirioCauchy
open Filter Topology

theorem cauchy_criterion (a : ℕ → ℝ) :
    (∃ L, Tendsto a atTop (𝓝 L)) ↔
      ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε := by
  have h : CauchySeq a ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε := by
    simp only [Metric.cauchySeq_iff, Real.dist_eq]
  rw [← h]
  exact ⟨fun ⟨L, hL⟩ => hL.cauchySeq, cauchySeq_tendsto_of_complete⟩

end Ch19.KritirioCauchy
