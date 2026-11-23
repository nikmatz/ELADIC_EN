-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 20 · Differentiation and Integration of Power Series · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch20.OroProsOro
open Filter Topology
open scoped NNReal ENNReal

-- f(x) = Σ cₙ (x - x₀)ⁿ, and R the radius of convergence of the power series Σ cₙ yⁿ
-- the differentiated series Σ (n + 1) cₙ₊₁ (x - x₀)ⁿ, that is, Σ n cₙ (x - x₀)ⁿ⁻¹, converges
theorem deriv_series_summable (c : ℕ → ℝ) (x₀ x : ℝ)
    (hx : ‖x - x₀‖ₑ < (FormalMultilinearSeries.ofScalars ℝ c).radius) :
    Summable (fun n => (n + 1) * c (n + 1) * (x - x₀) ^ n) := by
  set p := FormalMultilinearSeries.ofScalars ℝ c with hp
  have hs : Summable fun n => (x - x₀) ^ n • p.derivSeries.coeff n := by
    simpa using p.derivSeries.summable <|
      Metric.eball_subset_eball p.radius_le_radius_derivSeries <| by simpa using hx
  have h1 := (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).summable hs
  simp only [ContinuousLinearMap.apply_apply, smul_apply,
    FormalMultilinearSeries.derivSeries_coeff_one, hp, FormalMultilinearSeries.coeff_ofScalars,
    smul_eq_mul, nsmul_eq_mul] at h1
  refine h1.congr fun n => ?_
  push_cast
  ring

-- term-by-term differentiation: f'(x) = Σ (n + 1) cₙ₊₁ (x - x₀)ⁿ
theorem deriv_term_by_term (c : ℕ → ℝ) (x₀ x : ℝ)
    (hx : ‖x - x₀‖ₑ < (FormalMultilinearSeries.ofScalars ℝ c).radius) :
    HasDerivAt (fun y => ∑' n, c n * (y - x₀) ^ n)
      (∑' n, (n + 1) * c (n + 1) * (x - x₀) ^ n) x := by
  have h := (FormalMultilinearSeries.ofScalars ℝ c).hasDerivAt_sum hx
  -- the sum of the power series at y is Σ cₙ yⁿ
  have hsum : (FormalMultilinearSeries.ofScalars ℝ c).sum = fun y => ∑' n, c n * y ^ n := by
    funext y
    simp only [FormalMultilinearSeries.sum, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  rw [hsum] at h
  -- shift: y = x - x₀
  have h2 := h.comp_sub_const x x₀
  convert h2 using 1
  refine tsum_congr fun n => ?_
  simp only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

-- the integrated series Σ cₙ/(n + 1) (x - x₀)ⁿ⁺¹ converges absolutely
theorem integral_series_summable (c : ℕ → ℝ) (x₀ x : ℝ)
    (hx : ‖x - x₀‖ₑ < (FormalMultilinearSeries.ofScalars ℝ c).radius) :
    Summable (fun n => |c n / (n + 1) * (x - x₀) ^ (n + 1)|) := by
  have h := (FormalMultilinearSeries.ofScalars ℝ c).summable_norm_mul_pow hx
  simp only [FormalMultilinearSeries.ofScalars_norm, coe_nnNorm, Real.norm_eq_abs] at h
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) (h.mul_left |x - x₀|)
  -- |cₙ/(n + 1)| |x - x₀|ⁿ⁺¹ ≤ |x - x₀| · |cₙ| |x - x₀|ⁿ
  have h1 : |(n : ℝ) + 1| = (n : ℝ) + 1 := abs_of_pos (by positivity)
  have h2 : |c n| / ((n : ℝ) + 1) ≤ |c n| :=
    div_le_self (abs_nonneg _) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  rw [abs_mul, abs_div, abs_pow, h1, pow_succ]
  calc |c n| / ((n : ℝ) + 1) * (|x - x₀| ^ n * |x - x₀|)
      ≤ |c n| * (|x - x₀| ^ n * |x - x₀|) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = |x - x₀| * (|c n| * |x - x₀| ^ n) := by ring

-- term-by-term integration: G(x) = Σ cₙ/(n + 1) (x - x₀)ⁿ⁺¹ has derivative f(x)
theorem integral_term_by_term (c : ℕ → ℝ) (x₀ x : ℝ)
    (hx : ‖x - x₀‖ₑ < (FormalMultilinearSeries.ofScalars ℝ c).radius) :
    HasDerivAt (fun y => ∑' n, c n / (n + 1) * (y - x₀) ^ (n + 1))
      (∑' n, c n * (x - x₀) ^ n) x := by
  -- we choose r with |x - x₀| < r < R
  obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hx
  have hxr : |x - x₀| < r := by
    have h : ‖x - x₀‖₊ < r := ENNReal.coe_lt_coe.mp hr1
    rw [← Real.norm_eq_abs, ← coe_nnNorm]
    exact_mod_cast h
  -- the series Σ |cₙ| rⁿ converges, because r < R
  have hu : Summable (fun n => |c n| * (r : ℝ) ^ n) := by
    have h := (FormalMultilinearSeries.ofScalars ℝ c).summable_norm_mul_pow hr2
    simpa using h
  -- we differentiate term by term on the interval |y - x₀| < r
  refine hasDerivAt_tsum_of_isPreconnected (g := fun n y => c n / (n + 1) * (y - x₀) ^ (n + 1))
    (g' := fun n y => c n * (y - x₀) ^ n) hu Metric.isOpen_ball
    (convex_ball x₀ r).isPreconnected (fun n y _ => ?_) (fun n y hy => ?_)
    (Metric.mem_ball_self (lt_of_le_of_lt (abs_nonneg _) hxr)) ?_ ?_
  · -- each term cₙ/(n + 1) (y - x₀)ⁿ⁺¹ has derivative cₙ (y - x₀)ⁿ
    have h := ((hasDerivAt_pow (n + 1) (y - x₀)).comp_sub_const y x₀).const_mul (c n / (n + 1))
    convert h using 1
    rw [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, ← mul_assoc,
      div_mul_cancel₀ _ (by positivity : (n : ℝ) + 1 ≠ 0)]
  · -- bound on the interval: |cₙ (y - x₀)ⁿ| ≤ |cₙ| rⁿ
    rw [Metric.mem_ball, Real.dist_eq] at hy
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hy.le n) (abs_nonneg _)
  · -- at the center x₀ all the terms are 0
    simp
  · rw [Metric.mem_ball, Real.dist_eq]
    exact hxr

end Ch20.OroProsOro
