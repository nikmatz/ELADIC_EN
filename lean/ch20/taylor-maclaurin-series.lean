-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 20 · Taylor and Maclaurin Series · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch20.SeiraTaylor
open Filter Topology
open scoped Nat

-- T_n(x) = Σ from k = 0 to n of f^(k)(x₀)/k! · (x - x₀)^k, with derivatives within the set s
theorem taylor_partial_sum (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval f n s x₀ x =
      ∑ k ∈ Finset.range (n + 1), iteratedDerivWithin k f s x₀ / k ! * (x - x₀) ^ k := by
  rw [taylor_within_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_eq_mul]
  ring

-- the Taylor series has sum f(x) if and only if R_n(x) = f(x) - T_n(x) → 0
theorem taylor_series_iff (f : ℝ → ℝ) (s : Set ℝ) (x₀ x : ℝ) :
    Tendsto (fun n => taylorWithinEval f n s x₀ x) atTop (𝓝 (f x)) ↔
      Tendsto (fun n => f x - taylorWithinEval f n s x₀ x) atTop (𝓝 0) := by
  constructor
  · -- (⇒) if T_n(x) → f(x), then f(x) - T_n(x) → f(x) - f(x) = 0
    intro h
    have h1 := (tendsto_const_nhds (x := f x)).sub h
    rw [sub_self] at h1
    exact h1
  · -- (⇐) if R_n(x) → 0, then T_n(x) = f(x) - R_n(x) → f(x) - 0 = f(x)
    intro h
    have h1 := (tendsto_const_nhds (x := f x)).sub h
    rw [sub_zero] at h1
    have h2 : (fun n => f x - (f x - taylorWithinEval f n s x₀ x)) =
        fun n => taylorWithinEval f n s x₀ x := by
      funext n
      ring
    rw [h2] at h1
    exact h1

-- for x₀ = 0: the Maclaurin series
theorem maclaurin_iff (f : ℝ → ℝ) (s : Set ℝ) (x : ℝ) :
    Tendsto (fun n => taylorWithinEval f n s 0 x) atTop (𝓝 (f x)) ↔
      Tendsto (fun n => f x - taylorWithinEval f n s 0 x) atTop (𝓝 0) :=
  taylor_series_iff f s 0 x

-- Lagrange remainder: R_n(x) = f^(n+1)(ξ)/(n+1)! · (x - x₀)^(n+1), with ξ between x₀ and x
theorem lagrange_remainder (f : ℝ → ℝ) (n : ℕ) (x₀ x : ℝ) (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ n f (Set.uIcc x₀ x))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Set.uIcc x₀ x)) (Set.uIoo x₀ x)) :
    ∃ ξ ∈ Set.uIoo x₀ x, f x - taylorWithinEval f n (Set.uIcc x₀ x) x₀ x =
      iteratedDerivWithin (n + 1) f (Set.uIcc x₀ x) ξ * (x - x₀) ^ (n + 1) / (n + 1)! :=
  taylor_mean_remainder_lagrange hx hf hf'

-- at the center x₀ the Taylor series always converges to f(x₀)
theorem taylor_at_center (f : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ) :
    Tendsto (fun n => taylorWithinEval f n s x₀ x₀) atTop (𝓝 (f x₀)) := by
  simp only [taylorWithinEval_self]
  exact tendsto_const_nhds

end Ch20.SeiraTaylor
