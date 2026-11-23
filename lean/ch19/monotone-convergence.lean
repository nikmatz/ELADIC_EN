-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 19 · Monotone Convergence Theorem · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch19.MonotoniSygklisi
open Filter Topology

-- increasing and bounded above by M: it converges to the sup, and sup ≤ M
theorem monotone_convergence (a : ℕ → ℝ) (M : ℝ) (hmono : Monotone a) (hM : ∀ n, a n ≤ M) :
    Tendsto a atTop (𝓝 (⨆ n, a n)) ∧ (⨆ n, a n) ≤ M := by
  -- the set of terms is bounded above
  have hbdd : BddAbove (Set.range a) := ⟨M, by
    rintro _ ⟨n, rfl⟩
    exact hM n⟩
  refine ⟨?_, ciSup_le hM⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- sup - ε is not an upper bound: there exists N with a N > sup - ε
  obtain ⟨N, hN⟩ := exists_lt_of_lt_ciSup (show (⨆ n, a n) - ε < ⨆ n, a n by linarith)
  refine ⟨N, fun n hn => ?_⟩
  -- for n ≥ N: sup - ε < a N ≤ a n ≤ sup
  have h1 : a N ≤ a n := hmono hn
  have h2 : a n ≤ ⨆ n, a n := le_ciSup hbdd n
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem antitone_convergence (a : ℕ → ℝ) (m : ℝ) (hanti : Antitone a) (hm : ∀ n, m ≤ a n) :
    Tendsto a atTop (𝓝 (⨅ n, a n)) ∧ m ≤ ⨅ n, a n :=
  ⟨tendsto_atTop_ciInf hanti ⟨m, by
    rintro _ ⟨n, rfl⟩
    exact hm n⟩, le_ciInf hm⟩

end Ch19.MonotoniSygklisi
