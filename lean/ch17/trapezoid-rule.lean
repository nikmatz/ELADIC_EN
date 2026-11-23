-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 17 · The Trapezoidal Rule · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch17.KanonasTrapeziou

-- the Mathlib definition, with h = (b - a)/n, is written as in the book:
-- T_n = (h/2) (f(x₀) + 2 f(x₁) + … + 2 f(x_{n-1}) + f(xₙ))
theorem trapezoid_formula (f : ℝ → ℝ) (n : ℕ) (a b : ℝ) :
    trapezoidal_integral f n a b =
      (b - a) / n / 2 *
        (f a + 2 * ∑ k ∈ Finset.range (n - 1), f (a + (k + 1) * (b - a) / n) + f b) := by
  unfold trapezoidal_integral
  ring

-- error bound: |T_n - ∫ f| ≤ (b - a)³ M₂ / (12 n²)
theorem trapezoid_error (f : ℝ → ℝ) (a b M : ℝ) (n : ℕ) (hn : 0 < n) (hab : a ≤ b)
    (hf : ContDiffOn ℝ 2 f (Set.Icc a b))
    (hM : ∀ x, |iteratedDerivWithin 2 f (Set.Icc a b) x| ≤ M) :
    |trapezoidal_integral f n a b - ∫ x in a..b, f x| ≤ (b - a) ^ 3 / (12 * n ^ 2) * M := by
  rw [← Set.uIcc_of_le hab] at hf hM
  have h := trapezoidal_error_le_of_c2 hf hM hn
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
  unfold trapezoidal_error at h
  calc _ ≤ (b - a) ^ 3 * M / (12 * n ^ 2) := h
    _ = (b - a) ^ 3 / (12 * n ^ 2) * M := by ring

end Ch17.KanonasTrapeziou
