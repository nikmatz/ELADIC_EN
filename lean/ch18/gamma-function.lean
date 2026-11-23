-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 18 · The Gamma Function (Euler) · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch18.SynartisiGamma
open MeasureTheory
open scoped Nat

theorem gamma_integral (x : ℝ) (hx : 0 < x) :
    Real.Gamma x = ∫ t in Set.Ioi 0, Real.exp (-t) * t ^ (x - 1) :=
  Real.Gamma_eq_integral hx

theorem gamma_recursion (x : ℝ) (hx : 0 < x) : Real.Gamma (x + 1) = x * Real.Gamma x :=
  Real.Gamma_add_one hx.ne'

theorem gamma_factorial (n : ℕ) : Real.Gamma (n + 1) = n ! :=
  Real.Gamma_nat_eq_factorial n

theorem gamma_half : Real.Gamma (1 / 2) = Real.sqrt Real.pi :=
  Real.Gamma_one_half_eq

-- for s > 0: ∫ tⁿ e^(-st) dt from 0 to +∞ equals n!/s^(n+1)
theorem laplace_power (n : ℕ) (s : ℝ) (hs : 0 < s) :
    ∫ t in Set.Ioi 0, t ^ n * Real.exp (-(s * t)) = n ! / s ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := s) (by positivity) hs
  rw [add_sub_cancel_right, Real.Gamma_nat_eq_factorial, ← Nat.cast_add_one, Real.rpow_natCast] at h
  simp only [Real.rpow_natCast] at h
  rw [h, div_pow, one_pow, one_div_mul_eq_div]

-- for s ≤ 0 the integral diverges
theorem laplace_power_diverges (n : ℕ) (s : ℝ) (hs : s ≤ 0) :
    ¬ IntegrableOn (fun t => t ^ n * Real.exp (-(s * t))) (Set.Ioi 0) := by
  intro h
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioi (1 : ℝ)) := by
    refine Integrable.mono' (h.mono_set (Set.Ioi_subset_Ioi zero_le_one))
      aestronglyMeasurable_const (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    have ht1 : 1 ≤ t := (Set.mem_Ioi.mp ht).le
    rw [norm_one]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht1)
      (Real.one_le_exp (by nlinarith))
  simp at h1

end Ch18.SynartisiGamma
