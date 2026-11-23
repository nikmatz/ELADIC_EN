-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 19 · Bolzano–Weierstrass Theorem · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch19.BolzanoWeierstrass
open Filter Topology

-- bounded sequence: |a n| ≤ M for every n
theorem bolzano_weierstrass (a : ℕ → ℝ) (M : ℝ) (h : ∀ n, |a n| ≤ M) :
    ∃ L, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun k => a (φ k)) atTop (𝓝 L) := by
  obtain ⟨L, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (x := a) (Metric.isBounded_Icc (-M) M)
    (fun n => abs_le.mp (h n))
  exact ⟨L, φ, hφ, hlim⟩

end Ch19.BolzanoWeierstrass
