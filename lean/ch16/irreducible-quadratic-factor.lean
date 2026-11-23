-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 16 · Irreducible Quadratic Factor (Completing the Square) · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch16.AnagwgosTetragwnikos

theorem quadratic_factor (A B b c : ℝ) (hdisc : b ^ 2 - 4 * c < 0) (x : ℝ) :
    HasDerivAt (fun x => A / 2 * Real.log (x ^ 2 + b * x + c) +
        (B - A * b / 2) / Real.sqrt (c - b ^ 2 / 4) *
          Real.arctan ((x + b / 2) / Real.sqrt (c - b ^ 2 / 4)))
      ((A * x + B) / (x ^ 2 + b * x + c)) x := by
  -- k = √(c - b²/4) > 0
  set k := Real.sqrt (c - b ^ 2 / 4) with hk_def
  have hk : 0 < k := Real.sqrt_pos.mpr (by linarith)
  have hk0 : k ≠ 0 := hk.ne'
  have hk2 : k ^ 2 = c - b ^ 2 / 4 := Real.sq_sqrt (by linarith)
  -- completing the square: x² + bx + c = (x + b/2)² + k²
  have hsq : x ^ 2 + b * x + c = (x + b / 2) ^ 2 + k ^ 2 := by
    rw [hk2]
    ring
  have hpos : 0 < x ^ 2 + b * x + c := by
    rw [hsq]
    positivity
  -- logarithmic part: (ln(x² + bx + c))' = (2x + b)/(x² + bx + c)
  have h1 : HasDerivAt (fun x => x ^ 2 + b * x + c) (2 * x + b) x := by
    simpa using ((hasDerivAt_pow 2 x).add ((hasDerivAt_id' x).const_mul b)).add_const c
  have h2 := h1.log hpos.ne'
  -- arctangent: (arctan((x + b/2)/k))' = 1/(1 + ((x + b/2)/k)²) · 1/k
  have h3 : HasDerivAt (fun x => (x + b / 2) / k) (1 / k) x :=
    ((hasDerivAt_id' x).add_const (b / 2)).div_const k
  have h4 := h3.arctan
  -- we combine the two parts
  have h5 : HasDerivAt (fun x => A / 2 * Real.log (x ^ 2 + b * x + c) +
      (B - A * b / 2) / k * Real.arctan ((x + b / 2) / k))
      (A / 2 * ((2 * x + b) / (x ^ 2 + b * x + c)) +
        (B - A * b / 2) / k * (1 / (1 + ((x + b / 2) / k) ^ 2) * (1 / k))) x :=
    (h2.const_mul (A / 2)).add (h4.const_mul ((B - A * b / 2) / k))
  convert h5 using 1
  -- an algebraic identity remains
  have h6 : 1 + ((x + b / 2) / k) ^ 2 = ((x + b / 2) ^ 2 + k ^ 2) / k ^ 2 := by
    field_simp
    ring
  have hq : (x + b / 2) ^ 2 + k ^ 2 ≠ 0 := by
    rw [← hsq]
    exact hpos.ne'
  rw [h6, hsq]
  field_simp
  ring

theorem log_part (A b c : ℝ) (hdisc : b ^ 2 - 4 * c < 0) (x : ℝ) :
    HasDerivAt (fun x => A / 2 * Real.log (x ^ 2 + b * x + c))
      ((A * x + A * b / 2) / (x ^ 2 + b * x + c)) x := by
  have h := quadratic_factor A (A * b / 2) b c hdisc x
  simp only [sub_self, zero_div, zero_mul, add_zero] at h
  exact h

end Ch16.AnagwgosTetragwnikos
