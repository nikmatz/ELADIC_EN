-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 0 · De Moivre's Theorem · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch0.DeMoivre
open Complex

theorem de_moivre (θ : ℝ) (n : ℕ) :
    (cos θ + sin θ * I) ^ n = cos (n * θ) + sin (n * θ) * I := by
  induction n with
  | zero =>
    simp
  | succ k ih =>
    rw [pow_succ, ih]
    have h : ((k + 1 : ℕ) : ℂ) * θ = k * θ + θ := by push_cast; ring
    rw [h, cos_add, sin_add]
    linear_combination (sin (k * θ) * sin θ) * I_sq

theorem de_moivre_int (θ : ℝ) (n : ℤ) :
    (cos θ + sin θ * I) ^ n = cos (n * θ) + sin (n * θ) * I := by
  rw [← exp_mul_I, ← exp_mul_I, ← exp_intCast_mul, mul_assoc]

theorem exp_form (θ : ℝ) (n : ℕ) : exp (θ * I) ^ n = exp (n * θ * I) := by
  rw [← exp_natCast_mul, mul_assoc]

end Ch0.DeMoivre
