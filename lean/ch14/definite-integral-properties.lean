-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 14 · Properties of the Definite Integral · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch14.IdiotitesOloklirwmatos
open MeasureTheory

-- "f is integrable on [a,b]" is written IntervalIntegrable f volume a b

theorem reverse_limits (f : ℝ → ℝ) (a b : ℝ) : ∫ x in a..b, f x = -∫ x in b..a, f x :=
  intervalIntegral.integral_symm b a

theorem equal_limits (f : ℝ → ℝ) (a : ℝ) : ∫ x in a..a, f x = 0 :=
  intervalIntegral.integral_same

theorem linear_add (f g : ℝ → ℝ) (A B a b : ℝ) (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) :
    ∫ x in a..b, (A * f x + B * g x) = A * (∫ x in a..b, f x) + B * ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_add (hf.const_mul A) (hg.const_mul B),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem linear_sub (f g : ℝ → ℝ) (A B a b : ℝ) (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) :
    ∫ x in a..b, (A * f x - B * g x) = A * (∫ x in a..b, f x) - B * ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_sub (hf.const_mul A) (hg.const_mul B),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem additivity (f : ℝ → ℝ) (a b c : ℝ) (hac : IntervalIntegrable f volume a c)
    (hcb : IntervalIntegrable f volume c b) :
    ∫ x in a..b, f x = (∫ x in a..c, f x) + ∫ x in c..b, f x :=
  (intervalIntegral.integral_add_adjacent_intervals hac hcb).symm

theorem nonneg_integral (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : ∀ x ∈ Set.Icc a b, 0 ≤ f x) :
    0 ≤ ∫ x in a..b, f x :=
  intervalIntegral.integral_nonneg hab hf

theorem mono_integral (f g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) (hfg : ∀ x ∈ Set.Icc a b, f x ≤ g x) :
    ∫ x in a..b, f x ≤ ∫ x in a..b, g x :=
  intervalIntegral.integral_mono_on hab hf hg hfg

end Ch14.IdiotitesOloklirwmatos
