-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 10 · Derivatives of the Special Functions · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch10.PinakasParagogon

theorem d_pow (x : ℝ) (n : ℕ) : HasDerivAt (fun y => y ^ n) (n * x ^ (n - 1)) x :=
  hasDerivAt_pow n x

theorem d_exp (x : ℝ) : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x

theorem d_exp_base (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (fun y => a ^ y) (a ^ x * Real.log a) x :=
  (Real.hasStrictDerivAt_const_rpow ha x).hasDerivAt

theorem d_log (x : ℝ) (hx : x ≠ 0) : HasDerivAt Real.log (1 / x) x := by
  rw [one_div]
  exact Real.hasDerivAt_log hx

theorem d_logb (a x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y => Real.logb a y) (1 / (x * Real.log a)) x := by
  have h := (Real.hasDerivAt_log hx).div_const (Real.log a)
  have hfun : (fun y => Real.logb a y) = fun y => Real.log y / Real.log a := by
    funext y
    rw [Real.log_div_log]
  rw [hfun, one_div, mul_inv, ← div_eq_mul_inv]
  exact h

theorem d_sqrt (x : ℝ) (hx : x ≠ 0) : HasDerivAt (fun y => √y) (1 / (2 * √x)) x :=
  Real.hasDerivAt_sqrt hx

theorem d_sin (x : ℝ) : HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin x

theorem d_cos (x : ℝ) : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x

theorem d_tan (x : ℝ) (hx : Real.cos x ≠ 0) : HasDerivAt Real.tan (1 / Real.cos x ^ 2) x :=
  Real.hasDerivAt_tan hx

theorem d_cot (x : ℝ) (hx : Real.sin x ≠ 0) :
    HasDerivAt Real.cot (-(1 / Real.sin x ^ 2)) x := by
  have h := (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hx
  have hfun : Real.cos / Real.sin = Real.cot := by
    funext y
    rw [Pi.div_apply, Real.cot_eq_cos_div_sin]
  rw [hfun] at h
  convert h using 1
  rw [show -Real.sin x * Real.sin x - Real.cos x * Real.cos x = -1 by
    linear_combination -Real.sin_sq_add_cos_sq x]
  ring

theorem d_sec (x : ℝ) (hx : Real.cos x ≠ 0) :
    HasDerivAt (fun y => 1 / Real.cos y) (Real.sin x / Real.cos x ^ 2) x := by
  have h := (Real.hasDerivAt_cos x).inv hx
  rw [neg_neg] at h
  convert h using 1
  funext y
  rw [one_div, Pi.inv_apply]

theorem d_csc (x : ℝ) (hx : Real.sin x ≠ 0) :
    HasDerivAt (fun y => 1 / Real.sin y) (-Real.cos x / Real.sin x ^ 2) x := by
  have h := (Real.hasDerivAt_sin x).inv hx
  convert h using 1
  funext y
  rw [one_div, Pi.inv_apply]

theorem d_arcsin (x : ℝ) (h : |x| < 1) : HasDerivAt Real.arcsin (1 / √(1 - x ^ 2)) x := by
  rw [abs_lt] at h
  exact Real.hasDerivAt_arcsin h.1.ne' h.2.ne

theorem d_arccos (x : ℝ) (h : |x| < 1) : HasDerivAt Real.arccos (-(1 / √(1 - x ^ 2))) x := by
  rw [abs_lt] at h
  exact Real.hasDerivAt_arccos h.1.ne' h.2.ne

theorem d_arctan (x : ℝ) : HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x :=
  Real.hasDerivAt_arctan x

theorem d_sinh (x : ℝ) : HasDerivAt Real.sinh (Real.cosh x) x := Real.hasDerivAt_sinh x

theorem d_cosh (x : ℝ) : HasDerivAt Real.cosh (Real.sinh x) x := Real.hasDerivAt_cosh x

end Ch10.PinakasParagogon
