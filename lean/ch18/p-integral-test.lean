-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 18 · The p-Integral Test (Types I and II) · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch18.KritirioP
open MeasureTheory

-- (a) for a > 0, the integral of 1/x^p from a to +∞ converges exactly when p > 1
theorem p_test_infinity (a p : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => 1 / x ^ p) (Set.Ioi a) ↔ 1 < p := by
  have h : Set.EqOn (fun x : ℝ => 1 / x ^ p) (fun x => x ^ (-p)) (Set.Ioi a) := fun x hx => by
    simp only [Real.rpow_neg (ha.trans (Set.mem_Ioi.mp hx)).le, one_div]
  rw [integrableOn_congr_fun h measurableSet_Ioi, integrableOn_Ioi_rpow_iff ha]
  constructor <;> intro h <;> linarith

theorem p_value_infinity (p : ℝ) (hp : 1 < p) : ∫ x in Set.Ioi 1, 1 / x ^ p = 1 / (p - 1) := by
  have h : Set.EqOn (fun x : ℝ => 1 / x ^ p) (fun x => x ^ (-p)) (Set.Ioi 1) := fun x hx => by
    simp only [Real.rpow_neg (zero_le_one.trans (Set.mem_Ioi.mp hx).le), one_div]
  rw [setIntegral_congr_fun measurableSet_Ioi h, integral_Ioi_rpow_of_lt (a := -p) (by linarith) one_pos,
    Real.one_rpow]
  have h1 : -p + 1 ≠ 0 := ne_of_lt (by linarith)
  have h2 : p - 1 ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

-- (b) the integral of 1/x^p from 0 to 1 converges exactly when p < 1
theorem p_test_zero (p : ℝ) : IntegrableOn (fun x : ℝ => 1 / x ^ p) (Set.Ioo 0 1) ↔ p < 1 := by
  have h : Set.EqOn (fun x : ℝ => 1 / x ^ p) (fun x => x ^ (-p)) (Set.Ioo 0 1) := fun x hx => by
    simp only [Real.rpow_neg hx.1.le, one_div]
  rw [integrableOn_congr_fun h measurableSet_Ioo, intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]
  constructor <;> intro h <;> linarith

theorem p_value_zero (p : ℝ) (hp : p < 1) : ∫ x in (0 : ℝ)..1, 1 / x ^ p = 1 / (1 - p) := by
  have h : Set.EqOn (fun x : ℝ => 1 / x ^ p) (fun x => x ^ (-p)) (Set.uIcc 0 1) := fun x hx => by
    rw [Set.uIcc_of_le zero_le_one] at hx
    simp only [Real.rpow_neg hx.1, one_div]
  have h1 : -p + 1 ≠ 0 := ne_of_gt (by linarith)
  rw [intervalIntegral.integral_congr h, integral_rpow (r := -p) (Or.inl (by linarith)), Real.one_rpow,
    Real.zero_rpow h1]
  ring

end Ch18.KritirioP
