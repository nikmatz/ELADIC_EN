-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 20 · Cauchy–Hadamard Formula (Radius of Convergence) · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch20.CauchyHadamard
open Filter Topology
open scoped NNReal ENNReal

-- the power series Σ cₙ yⁿ with y = x - x₀, and its radius of convergence R in [0, +∞]
-- Cauchy–Hadamard formula: R = 1 / limsup ⁿ√|cₙ|, with 1/0 = +∞ and 1/(+∞) = 0
theorem cauchy_hadamard (c : ℕ → ℝ) :
    (FormalMultilinearSeries.ofScalars ℝ c).radius =
      (limsup (fun n => ((‖c n‖₊ ^ (1 / (n : ℝ)) : ℝ≥0) : ℝ≥0∞)) atTop)⁻¹ := by
  have h := (FormalMultilinearSeries.ofScalars ℝ c).radius_inv_eq_limsup
  have hn : ∀ n, ‖FormalMultilinearSeries.ofScalars ℝ c n‖₊ = ‖c n‖₊ := fun n =>
    NNReal.eq (FormalMultilinearSeries.ofScalars_norm ℝ c n)
  simp only [hn] at h
  rw [← h, inv_inv]

-- for |x - x₀| < R the series converges absolutely
theorem converges_inside (c : ℕ → ℝ) (x₀ x : ℝ)
    (hx : ‖x - x₀‖ₑ < (FormalMultilinearSeries.ofScalars ℝ c).radius) :
    Summable (fun n => |c n * (x - x₀) ^ n|) := by
  have h := (FormalMultilinearSeries.ofScalars ℝ c).summable_norm_mul_pow hx
  simp only [FormalMultilinearSeries.ofScalars_norm, coe_nnNorm, Real.norm_eq_abs] at h
  simpa [abs_mul, abs_pow] using h

-- for |x - x₀| > R the partial sums do not converge
theorem diverges_outside (c : ℕ → ℝ) (x₀ x : ℝ)
    (hx : (FormalMultilinearSeries.ofScalars ℝ c).radius < ‖x - x₀‖ₑ) :
    ¬ ∃ S, Tendsto (fun N => ∑ n ∈ Finset.range N, c n * (x - x₀) ^ n) atTop (𝓝 S) := by
  rintro ⟨S, hS⟩
  -- necessary condition: cₙ (x - x₀)ⁿ → 0
  have h0 : Tendsto (fun n => c n * (x - x₀) ^ n) atTop (𝓝 0) := by
    have h1 := (hS.comp (tendsto_add_atTop_nat 1)).sub hS
    simp only [Function.comp_def, Finset.sum_range_succ, add_sub_cancel_left, sub_self] at h1
    exact h1
  -- then |x - x₀| ≤ R, a contradiction
  have h2 : (‖x - x₀‖₊ : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℝ c).radius := by
    refine (FormalMultilinearSeries.ofScalars ℝ c).le_radius_of_tendsto (r := ‖x - x₀‖₊) (l := 0) ?_
    simpa [abs_mul, abs_pow] using h0.abs
  exact absurd h2 (not_le.mpr hx)

-- practical form: if |cₙ / cₙ₊₁| → R with 0 < R < +∞, the radius is R
theorem ratio_formula (c : ℕ → ℝ) (R : ℝ≥0) (hR : R ≠ 0)
    (h : Tendsto (fun n => |c n / c (n + 1)|) atTop (𝓝 (R : ℝ))) :
    (FormalMultilinearSeries.ofScalars ℝ c).radius = R :=
  FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto ℝ c hR (by simpa [abs_div] using h)

-- if |cₙ / cₙ₊₁| → +∞, the radius is +∞
theorem ratio_formula_top (c : ℕ → ℝ) (hc : ∀ᶠ n in atTop, c n ≠ 0)
    (h : Tendsto (fun n => |c n / c (n + 1)|) atTop atTop) :
    (FormalMultilinearSeries.ofScalars ℝ c).radius = ⊤ := by
  refine FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℝ c hc ?_
  have h1 := h.inv_tendsto_atTop
  simpa [abs_div, Pi.inv_def] using h1

-- if |cₙ / cₙ₊₁| → 0, the radius is 0
theorem ratio_formula_zero (c : ℕ → ℝ) (hc : ∀ᶠ n in atTop, c n ≠ 0)
    (h : Tendsto (fun n => |c n / c (n + 1)|) atTop (𝓝 0)) :
    (FormalMultilinearSeries.ofScalars ℝ c).radius = 0 := by
  refine FormalMultilinearSeries.ofScalars_radius_eq_zero_of_tendsto ℝ c ?_
  -- the ratio is positive for large n, so its reciprocal tends to +∞
  have hpos : ∀ᶠ n in atTop, 0 < |c n / c (n + 1)| := by
    filter_upwards [hc, (tendsto_add_atTop_nat 1).eventually hc] with n h1 h2
    exact abs_pos.mpr (div_ne_zero h1 h2)
  have h1 : Tendsto (fun n => |c n / c (n + 1)|) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨h, hpos⟩
  have h2 := tendsto_inv_nhdsGT_zero.comp h1
  simpa [Function.comp_def, abs_div] using h2

end Ch20.CauchyHadamard
