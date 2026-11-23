-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 13 · Table of Basic Integrals · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch13.PinakasOloklirwmatwn

-- each formula ∫ f(x) dx = F(x) + C is written as: F has derivative f

theorem int_pow (n : ℕ) (x : ℝ) : HasDerivAt (fun x : ℝ => x ^ (n + 1) / (n + 1)) (x ^ n) x := by
  have h := (hasDerivAt_pow (n + 1) x).div_const ((n : ℝ) + 1)
  rw [Nat.add_sub_cancel] at h
  convert h using 1
  push_cast
  field_simp

theorem int_rpow (r x : ℝ) (hr : r ≠ -1) (hx : 0 < x) :
    HasDerivAt (fun x => x ^ (r + 1) / (r + 1)) (x ^ r) x := by
  have hr1 : r + 1 ≠ 0 := fun h => hr (by linarith)
  have h := (Real.hasDerivAt_rpow_const (p := r + 1) (Or.inl hx.ne')).div_const (r + 1)
  convert h using 1
  rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hr1]

theorem int_inv (x : ℝ) (hx : x ≠ 0) : HasDerivAt (fun x => Real.log |x|) (1 / x) x := by
  have h : (fun x : ℝ => Real.log |x|) = Real.log := by
    funext y
    exact Real.log_abs y
  rw [h, one_div]
  exact Real.hasDerivAt_log hx

theorem int_exp (x : ℝ) : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x

theorem int_exp_base (a x : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    HasDerivAt (fun x => a ^ x / Real.log a) (a ^ x) x := by
  have hlog : Real.log a ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ha ha1
  have h := (Real.hasStrictDerivAt_const_rpow ha x).hasDerivAt.div_const (Real.log a)
  convert h using 1
  rw [mul_div_cancel_right₀ _ hlog]

theorem int_sin (x : ℝ) : HasDerivAt (fun x => -Real.cos x) (Real.sin x) x := by
  have h : HasDerivAt (fun x => -Real.cos x) (-(-Real.sin x)) x := (Real.hasDerivAt_cos x).neg
  rw [neg_neg] at h
  exact h

theorem int_cos (x : ℝ) : HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin x

theorem int_sec_sq (x : ℝ) (hx : Real.cos x ≠ 0) : HasDerivAt Real.tan (1 / Real.cos x ^ 2) x :=
  Real.hasDerivAt_tan hx

theorem int_csc_sq (x : ℝ) (hx : Real.sin x ≠ 0) :
    HasDerivAt (fun x => -Real.cot x) (1 / Real.sin x ^ 2) x := by
  have h := (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hx
  have hfun : Real.cos / Real.sin = Real.cot := by
    funext y
    rw [Pi.div_apply, Real.cot_eq_cos_div_sin]
  rw [hfun] at h
  have h2 : HasDerivAt (fun x => -Real.cot x)
      (-((-Real.sin x * Real.sin x - Real.cos x * Real.cos x) / Real.sin x ^ 2)) x := h.neg
  convert h2 using 1
  rw [show -Real.sin x * Real.sin x - Real.cos x * Real.cos x = -1 by
    linear_combination -Real.sin_sq_add_cos_sq x]
  ring

theorem int_sec_tan (x : ℝ) (hx : Real.cos x ≠ 0) :
    HasDerivAt (fun x => 1 / Real.cos x) (1 / Real.cos x * Real.tan x) x := by
  have h := (Real.hasDerivAt_cos x).inv hx
  rw [neg_neg] at h
  have h2 : HasDerivAt (fun x => 1 / Real.cos x) (Real.sin x / Real.cos x ^ 2) x := by
    convert h using 1
    funext y
    rw [one_div, Pi.inv_apply]
  convert h2 using 1
  rw [Real.tan_eq_sin_div_cos, div_mul_div_comm, one_mul, sq]

theorem int_csc_cot (x : ℝ) (hx : Real.sin x ≠ 0) :
    HasDerivAt (fun x => -(1 / Real.sin x)) (1 / Real.sin x * Real.cot x) x := by
  have h := (Real.hasDerivAt_sin x).inv hx
  have h2 : HasDerivAt (fun x => -(1 / Real.sin x)) (-(-Real.cos x / Real.sin x ^ 2)) x := by
    have h3 := h.neg
    convert h3 using 1
    funext y
    rw [one_div, Pi.neg_apply, Pi.inv_apply]
  convert h2 using 1
  rw [Real.cot_eq_cos_div_sin, div_mul_div_comm, one_mul, sq, neg_div, neg_neg]

theorem int_tan (x : ℝ) (hx : Real.cos x ≠ 0) :
    HasDerivAt (fun x => -Real.log |Real.cos x|) (Real.tan x) x := by
  have h1 : HasDerivAt (fun x => Real.log (Real.cos x)) (-Real.sin x / Real.cos x) x :=
    (Real.hasDerivAt_cos x).log hx
  have h2 : (fun x => -Real.log |Real.cos x|) = fun x => -Real.log (Real.cos x) := by
    funext y
    rw [Real.log_abs]
  have h3 : HasDerivAt (fun x => -Real.log (Real.cos x)) (-(-Real.sin x / Real.cos x)) x :=
    h1.neg
  rw [h2, Real.tan_eq_sin_div_cos]
  convert h3 using 1
  rw [neg_div, neg_neg]

theorem int_cot (x : ℝ) (hx : Real.sin x ≠ 0) :
    HasDerivAt (fun x => Real.log |Real.sin x|) (Real.cot x) x := by
  have h1 : HasDerivAt (fun x => Real.log (Real.sin x)) (Real.cos x / Real.sin x) x :=
    (Real.hasDerivAt_sin x).log hx
  have h2 : (fun x => Real.log |Real.sin x|) = fun x => Real.log (Real.sin x) := by
    funext y
    rw [Real.log_abs]
  rw [h2, Real.cot_eq_cos_div_sin]
  exact h1

theorem int_one_add_sq (x : ℝ) : HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x :=
  Real.hasDerivAt_arctan x

theorem int_sqrt_one_sub_sq (x : ℝ) (h : |x| < 1) :
    HasDerivAt Real.arcsin (1 / √(1 - x ^ 2)) x := by
  rw [abs_lt] at h
  exact Real.hasDerivAt_arcsin h.1.ne' h.2.ne

theorem int_a_sq_add_sq (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun x => 1 / a * Real.arctan (x / a)) (1 / (a ^ 2 + x ^ 2)) x := by
  have h1 : HasDerivAt (fun x => x / a) (1 / a) x := by
    simpa using (hasDerivAt_id x).div_const a
  have hat := Real.hasDerivAt_arctan (x / a)
  have h2 := hat.comp x h1
  have h3 : HasDerivAt (fun x => 1 / a * Real.arctan (x / a))
      (1 / a * (1 / (1 + (x / a) ^ 2) * (1 / a))) x := h2.const_mul (1 / a)
  convert h3 using 1
  have hden : a ^ 2 + x ^ 2 ≠ 0 := by positivity
  field_simp

theorem int_sqrt_a_sq_sub_sq (a x : ℝ) (ha : 0 < a) (hx : |x| < a) :
    HasDerivAt (fun x => Real.arcsin (x / a)) (1 / √(a ^ 2 - x ^ 2)) x := by
  have ha0 : a ≠ 0 := ha.ne'
  have hxa : |x / a| < 1 := by
    rw [abs_div, abs_of_pos ha, div_lt_one ha]
    exact hx
  rw [abs_lt] at hxa
  have h1 : HasDerivAt (fun x => x / a) (1 / a) x := by
    simpa using (hasDerivAt_id x).div_const a
  have has := Real.hasDerivAt_arcsin hxa.1.ne' hxa.2.ne
  have h2 := has.comp x h1
  have hsq : √(a ^ 2 - x ^ 2) = a * √(1 - (x / a) ^ 2) := by
    have h : a ^ 2 - x ^ 2 = a ^ 2 * (1 - (x / a) ^ 2) := by
      field_simp
    rw [h, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  have h3 : HasDerivAt (fun x => Real.arcsin (x / a)) (1 / √(1 - (x / a) ^ 2) * (1 / a)) x := h2
  convert h3 using 1
  rw [hsq, one_div_mul_one_div, mul_comm]

end Ch13.PinakasOloklirwmatwn
