-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 11 · Second Derivative Test for Extrema · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch11.KritirioDeuterisParagogou

theorem second_deriv_min (f : ℝ → ℝ) (x₀ : ℝ) (hc : ContinuousAt f x₀) (hd : deriv f x₀ = 0)
    (hpos : 0 < deriv (deriv f) x₀) : IsLocalMin f x₀ :=
  isLocalMin_of_deriv_deriv_pos hpos hd hc

theorem second_deriv_max (f : ℝ → ℝ) (x₀ : ℝ) (hc : ContinuousAt f x₀) (hd : deriv f x₀ = 0)
    (hneg : deriv (deriv f) x₀ < 0) : IsLocalMax f x₀ :=
  isLocalMax_of_deriv_deriv_neg hneg hd hc

-- when f''(x₀) = 0 the test is inconclusive: x⁴ has a minimum at 0, x³ has no extremum
theorem quartic : deriv (fun x : ℝ => x ^ 4) 0 = 0 ∧ deriv (deriv (fun x : ℝ => x ^ 4)) 0 = 0 ∧
    IsLocalMin (fun x : ℝ => x ^ 4) 0 := by
  have h1 : deriv (fun x : ℝ => x ^ 4) = fun x => 4 * x ^ 3 := by
    funext x
    rw [deriv_pow_field]
    norm_num
  refine ⟨by rw [h1]; norm_num, ?_, ?_⟩
  · rw [h1, deriv_const_mul _ (differentiableAt_pow 3), deriv_pow_field]
    norm_num
  · exact Filter.Eventually.of_forall fun x => by
      show (0 : ℝ) ^ 4 ≤ x ^ 4
      rw [zero_pow (by norm_num)]
      positivity

theorem cubic : deriv (fun x : ℝ => x ^ 3) 0 = 0 ∧ deriv (deriv (fun x : ℝ => x ^ 3)) 0 = 0 ∧
    ¬ IsLocalExtr (fun x : ℝ => x ^ 3) 0 := by
  have h1 : deriv (fun x : ℝ => x ^ 3) = fun x => 3 * x ^ 2 := by
    funext x
    rw [deriv_pow_field]
    norm_num
  refine ⟨by rw [h1]; norm_num, ?_, ?_⟩
  · rw [h1, deriv_const_mul _ (differentiableAt_pow 2), deriv_pow_field]
    norm_num
  · have hpt : ∀ ε : ℝ, 0 < ε → dist (ε / 2) 0 < ε ∧ dist (-(ε / 2)) 0 < ε := by
      intro ε hε
      rw [Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, abs_neg, abs_of_pos (half_pos hε)]
      constructor <;> linarith
    rintro (h | h)
    · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
      have h2 : (0 : ℝ) ^ 3 ≤ (-(ε / 2)) ^ 3 := hball (hpt ε hε).2
      have h3 : 0 < (ε / 2) ^ 3 := pow_pos (half_pos hε) 3
      linarith
    · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
      have h2 : (ε / 2) ^ 3 ≤ (0 : ℝ) ^ 3 := hball (hpt ε hε).1
      have h3 : 0 < (ε / 2) ^ 3 := pow_pos (half_pos hε) 3
      linarith

end Ch11.KritirioDeuterisParagogou
