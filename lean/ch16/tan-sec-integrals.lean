-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 16 · Integrals with tan and sec · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch16.TanSec

-- we write sec x = 1/cos x

-- ∫ sec² x dx = tan x + C
theorem int_sec_sq (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt Real.tan (1 / Real.cos x ^ 2) x :=
  Real.hasDerivAt_tan hc

-- ∫ sec x tan x dx = sec x + C
theorem int_sec_tan (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt (fun x => 1 / Real.cos x) (1 / Real.cos x * Real.tan x) x := by
  have h := (hasDerivAt_const x (1 : ℝ)).fun_div (Real.hasDerivAt_cos x) hc
  convert h using 1
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

-- ∫ sec x dx = ln|sec x + tan x| + C
theorem int_sec (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt (fun x => Real.log |1 / Real.cos x + Real.tan x|) (1 / Real.cos x) x := by
  -- in Mathlib, ln|t| = ln t
  simp only [Real.log_abs]
  -- when cos x ≠ 0, sin x ≠ -1
  have hs : 1 + Real.sin x ≠ 0 := by
    intro h
    have h1 : Real.sin x = -1 := by linarith
    have h2 := Real.sin_sq_add_cos_sq x
    rw [h1] at h2
    have h3 : Real.cos x ^ 2 = 0 := by linarith
    exact hc (pow_eq_zero_iff two_ne_zero |>.mp h3)
  -- sec x + tan x = (1 + sin x)/cos x ≠ 0
  have hne : 1 / Real.cos x + Real.tan x ≠ 0 := by
    rw [Real.tan_eq_sin_div_cos, ← add_div]
    exact div_ne_zero hs hc
  -- (sec x + tan x)' = sec x tan x + sec² x
  have h1 : HasDerivAt (fun x => 1 / Real.cos x + Real.tan x)
      (1 / Real.cos x * Real.tan x + 1 / Real.cos x ^ 2) x :=
    (int_sec_tan x hc).add (int_sec_sq x hc)
  -- logarithm rule
  have h2 := h1.log hne
  convert h2 using 1
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  ring

theorem int_tan (x : ℝ) (hc : Real.cos x ≠ 0) :
    HasDerivAt (fun x => Real.log |1 / Real.cos x|) (Real.tan x) x := by
  simp only [Real.log_abs]
  have h := (int_sec_tan x hc).log (one_div_ne_zero hc)
  convert h using 1
  rw [Real.tan_eq_sin_div_cos]
  field_simp

end Ch16.TanSec
