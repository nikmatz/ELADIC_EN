-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 12 · Criteria for Asymptotes · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch12.Asymptotes
open Filter Topology Polynomial

-- (i) vertical asymptote: at the root x₀ of the denominator, with numerator ≠ 0, |p/q| → +∞
theorem vertical_asymptote (p q : ℝ → ℝ) (x₀ : ℝ) (hp : ContinuousAt p x₀)
    (hq : ContinuousAt q x₀) (hq0 : q x₀ = 0) (hp0 : p x₀ ≠ 0)
    (hqne : ∀ᶠ x in 𝓝[≠] x₀, q x ≠ 0) :
    Tendsto (fun x => |p x / q x|) (𝓝[≠] x₀) atTop := by
  have h1 : Tendsto (fun x => |p x|) (𝓝[≠] x₀) (𝓝 |p x₀|) :=
    (hp.tendsto.abs).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun x => |q x|) (𝓝[≠] x₀) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h := (hq.tendsto.abs).mono_left (nhdsWithin_le_nhds (s := {x₀}ᶜ))
      rwa [hq0, abs_zero] at h
    · filter_upwards [hqne] with x hx
      exact abs_pos.mpr hx
  have h3 := h1.pos_mul_atTop (abs_pos.mpr hp0) (tendsto_inv_nhdsGT_zero.comp h2)
  refine h3.congr (fun x => ?_)
  simp [div_eq_mul_inv]

-- (ii) horizontal asymptote y = 0 when deg P < deg Q
theorem horizontal_zero (P Q : ℝ[X]) (hdeg : P.degree < Q.degree) :
    Tendsto (fun x => P.eval x / Q.eval x) atTop (𝓝 0) :=
  Polynomial.div_tendsto_atTop_zero_of_degree_lt hdeg

-- (ii) when deg P = deg Q, the asymptote is the ratio of the leading coefficients
theorem horizontal_ratio (P Q : ℝ[X]) (hdeg : P.degree = Q.degree) :
    Tendsto (fun x => P.eval x / Q.eval x) atTop (𝓝 (P.leadingCoeff / Q.leadingCoeff)) :=
  Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq hdeg

-- (iii) the quotient S of the division P / Q: the difference P/Q - S tends to 0
theorem minus_quotient (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    Tendsto (fun x => P.eval x / Q.eval x - (P / Q).eval x) atTop (𝓝 0) := by
  have hR : Tendsto (fun x => (P % Q).eval x / Q.eval x) atTop (𝓝 0) :=
    Polynomial.div_tendsto_atTop_zero_of_degree_lt (Polynomial.degree_mod_lt P hQ)
  refine hR.congr' ?_
  have hfin : {x | Q.IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hQ
  filter_upwards [Filter.atTop_le_cofinite hfin.compl_mem_cofinite] with x hx
  have hx' : Q.eval x ≠ 0 := hx
  have he : P.eval x = Q.eval x * (P / Q).eval x + (P % Q).eval x := by
    rw [← Polynomial.eval_mul, ← Polynomial.eval_add, EuclideanDomain.div_add_mod]
  rw [he, add_div, mul_div_cancel_left₀ _ hx']
  ring

-- general criterion: y = αx + β is an asymptote at +∞ exactly when f(x)/x → α and f(x) - αx → β
theorem oblique_iff (f : ℝ → ℝ) (α β : ℝ) :
    Tendsto (fun x => f x - (α * x + β)) atTop (𝓝 0) ↔
      Tendsto (fun x => f x / x) atTop (𝓝 α) ∧ Tendsto (fun x => f x - α * x) atTop (𝓝 β) := by
  constructor
  · intro h
    have h2 : Tendsto (fun x => f x - α * x) atTop (𝓝 β) := by
      have h' := h.add_const β
      rw [zero_add] at h'
      refine h'.congr (fun x => ?_)
      ring
    refine ⟨?_, h2⟩
    have h3 : Tendsto (fun x => (f x - α * x) / x) atTop (𝓝 0) := h2.div_atTop tendsto_id
    have h4 := h3.add_const α
    rw [zero_add] at h4
    refine h4.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with x hx
    rw [sub_div, mul_div_assoc, div_self hx, mul_one, sub_add_cancel]
  · rintro ⟨_, h2⟩
    have h' := h2.sub_const β
    rw [sub_self] at h'
    refine h'.congr (fun x => ?_)
    ring

end Ch12.Asymptotes
