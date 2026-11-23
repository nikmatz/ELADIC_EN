-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 8 · Properties of the Hyperbolic Functions · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch8.YperbolikesIdiotites
open Real

theorem cosh_sq_minus_sinh_sq (x : ℝ) : cosh x ^ 2 - sinh x ^ 2 = 1 := by
  rw [Real.cosh_eq, Real.sinh_eq]
  have h : exp x * exp (-x) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  linear_combination h

theorem cosh_is_even (x : ℝ) : cosh (-x) = cosh x := Real.cosh_neg x

theorem sinh_is_odd (x : ℝ) : sinh (-x) = -sinh x := Real.sinh_neg x

theorem tanh_is_odd (x : ℝ) : tanh (-x) = -tanh x := Real.tanh_neg x

theorem sinh_strictly_increasing : StrictMono sinh := Real.sinh_strictMono

theorem tanh_has_deriv (x : ℝ) : HasDerivAt tanh (1 / cosh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have hfun : sinh / cosh = tanh := by
    funext y
    rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
  rw [hfun] at h
  convert h using 1
  rw [← cosh_sq_minus_sinh_sq x]
  ring

theorem tanh_strictly_increasing : StrictMono tanh :=
  strictMono_of_deriv_pos fun x => by
    rw [(tanh_has_deriv x).deriv]
    exact one_div_pos.mpr (pow_pos (Real.cosh_pos x) 2)

theorem cosh_decreasing_left (x y : ℝ) (hy : y ≤ 0) (hxy : x < y) : cosh y < cosh x := by
  rw [Real.cosh_lt_cosh, abs_of_nonpos hy, abs_of_nonpos (hxy.le.trans hy)]
  linarith

theorem cosh_increasing_right (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) : cosh x < cosh y := by
  rw [Real.cosh_lt_cosh, abs_of_nonneg hx, abs_of_nonneg (hx.trans hxy.le)]
  exact hxy

theorem cosh_at_zero : cosh 0 = 1 := by
  rw [Real.cosh_eq, neg_zero, Real.exp_zero]
  norm_num

theorem sinh_of_sum (x y : ℝ) : sinh (x + y) = sinh x * cosh y + cosh x * sinh y :=
  Real.sinh_add x y

theorem cosh_of_sum (x y : ℝ) : cosh (x + y) = cosh x * cosh y + sinh x * sinh y :=
  Real.cosh_add x y

end Ch8.YperbolikesIdiotites
