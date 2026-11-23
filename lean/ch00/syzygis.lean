-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 0 · Properties of the Conjugate · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch0.Syzygis
open Complex ComplexConjugate

theorem double_conj (z : ℂ) : conj (conj z) = z := conj_conj z

theorem real_iff (z : ℂ) : conj z = z ↔ ∃ r : ℝ, z = r := conj_eq_iff_real

theorem imaginary_iff (z : ℂ) : conj z = -z ↔ z.re = 0 := by
  rw [Complex.ext_iff]
  simp only [conj_re, neg_re, conj_im, neg_im]
  constructor
  · rintro ⟨h, -⟩
    linarith
  · intro h
    exact ⟨by linarith, by simp⟩

theorem re_formula (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := re_eq_add_conj z

theorem im_formula (z : ℂ) : (z.im : ℂ) = (z - conj z) / (2 * I) := im_eq_sub_conj z

theorem mul_conj_eq (z : ℂ) : z * conj z = (‖z‖ ^ 2 : ℝ) := by
  rw [mul_conj, normSq_eq_norm_sq]

theorem conj_sum (z w : ℂ) : conj (z + w) = conj z + conj w := by
  apply Complex.ext
  · simp only [conj_re, add_re]
  · simp only [conj_im, add_im]
    ring

theorem conj_product (z w : ℂ) : conj (z * w) = conj z * conj w := by
  apply Complex.ext
  · simp only [conj_re, mul_re, conj_im]
    ring
  · simp only [conj_im, mul_im, conj_re]
    ring

theorem conj_quotient (z w : ℂ) : conj (z / w) = conj z / conj w := map_div₀ conj z w

end Ch0.Syzygis
