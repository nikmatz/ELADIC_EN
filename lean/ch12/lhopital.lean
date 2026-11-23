-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 12 · L'Hôpital's Rule · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch12.LHopital
open Filter Topology

-- form 0/0 as x → x₀ (x ≠ x₀); l can be 𝓝 L, atTop or atBot
theorem lhopital_zero_point (f g f' g' : ℝ → ℝ) (x₀ : ℝ) (l : Filter ℝ)
    (hff' : ∀ᶠ x in 𝓝[≠] x₀, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝[≠] x₀, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in 𝓝[≠] x₀, g' x ≠ 0)
    (hf : Tendsto f (𝓝[≠] x₀) (𝓝 0)) (hg : Tendsto g (𝓝[≠] x₀) (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) (𝓝[≠] x₀) l) :
    Tendsto (fun x => f x / g x) (𝓝[≠] x₀) l :=
  HasDerivAt.lhopital_zero_nhdsNE hff' hgg' hg' hf hg hdiv

-- form 0/0 as x → +∞
theorem lhopital_zero_infty (f g f' g' : ℝ → ℝ) (l : Filter ℝ)
    (hff' : ∀ᶠ x in atTop, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in atTop, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in atTop, g' x ≠ 0)
    (hf : Tendsto f atTop (𝓝 0)) (hg : Tendsto g atTop (𝓝 0))
    (hdiv : Tendsto (fun x => f' x / g' x) atTop l) :
    Tendsto (fun x => f x / g x) atTop l :=
  HasDerivAt.lhopital_zero_atTop hff' hgg' hg' hf hg hdiv

-- form ⋆/∞ as x → +∞ (|g| → +∞), with finite limit L: our own proof
theorem lhopital_infty_atTop (f g f' g' : ℝ → ℝ) (a L : ℝ)
    (hff' : ∀ x ∈ Set.Ioi a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Set.Ioi a, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.Ioi a, g' x ≠ 0)
    (hg : Tendsto (fun x => |g x|) atTop atTop)
    (hdiv : Tendsto (fun x => f' x / g' x) atTop (𝓝 L)) :
    Tendsto (fun x => f x / g x) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- beyond some t₀ the ratio f'/g' is within ε/2 of L
  obtain ⟨t₀, ht₀⟩ := Metric.tendsto_atTop.mp hdiv (ε / 2) (half_pos hε)
  obtain ⟨t₁, ht₁0, ht₁a⟩ : ∃ t₁, t₀ ≤ t₁ ∧ a < t₁ :=
    ⟨max t₀ (a + 1), le_max_left _ _, lt_of_lt_of_le (by linarith) (le_max_right _ _)⟩
  -- a constant K and an N beyond which |g(x)| > 2K/ε
  obtain ⟨K, hK⟩ : ∃ K, K = |f t₁| + (|L| + ε / 2) * |g t₁| := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact add_nonneg (abs_nonneg _) (mul_nonneg (by linarith [abs_nonneg L]) (abs_nonneg _))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hg.eventually_gt_atTop (2 * K / ε))
  refine ⟨max N (t₁ + 1), fun x hx => ?_⟩
  have hxN : N ≤ x := le_of_max_le_left hx
  have hxt : t₁ < x := by linarith [le_of_max_le_right hx]
  have hgx : 2 * K / ε < |g x| := hN x hxN
  -- Cauchy's mean value theorem on [t₁, x]
  have hfc : ContinuousOn f (Set.Icc t₁ x) := fun z hz =>
    (hff' z (lt_of_lt_of_le ht₁a hz.1)).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Set.Icc t₁ x) := fun z hz =>
    (hgg' z (lt_of_lt_of_le ht₁a hz.1)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcm⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' hxt hfc
    (fun z hz => hff' z (ht₁a.trans hz.1)) g g' hgc (fun z hz => hgg' z (ht₁a.trans hz.1))
  have hgne : g x - g t₁ ≠ 0 := by
    intro h0
    obtain ⟨d, hd, hd0⟩ := exists_hasDerivAt_eq_zero hxt hgc (by linarith)
      (fun z hz => hgg' z (ht₁a.trans hz.1))
    exact hg' d (ht₁a.trans hd.1) hd0
  have hc0 : g' c ≠ 0 := hg' c (ht₁a.trans hc.1)
  obtain ⟨q, hq⟩ : ∃ q, q = (f x - f t₁) / (g x - g t₁) := ⟨_, rfl⟩
  have hqc : q = f' c / g' c := by
    rw [hq, div_eq_div_iff hgne hc0]
    linear_combination -hcm
  have hqL : |q - L| < ε / 2 := by
    rw [hqc, ← Real.dist_eq]
    exact ht₀ c (ht₁0.trans hc.1.le)
  have hq_abs : |q| ≤ |L| + ε / 2 := by
    have := abs_sub_abs_le_abs_sub q L
    linarith
  -- f(x)/g(x) - L = (q - L) + (f(t₁) - q g(t₁))/g(x)
  have hgpos : 0 < |g x| := lt_of_le_of_lt (div_nonneg (by linarith) hε.le) hgx
  have hgx0 : g x ≠ 0 := abs_pos.mp hgpos
  have hfx : f x = q * g x + (f t₁ - q * g t₁) := by
    have h := div_mul_cancel₀ (f x - f t₁) hgne
    rw [← hq] at h
    linear_combination -h
  have hsplit : f x / g x - L = (q - L) + (f t₁ - q * g t₁) / g x := by
    rw [hfx, add_div, mul_div_cancel_right₀ q hgx0]
    ring
  have hbound : |f t₁ - q * g t₁| ≤ K := by
    rw [hK]
    calc |f t₁ - q * g t₁| ≤ |f t₁| + |q * g t₁| := abs_sub _ _
      _ = |f t₁| + |q| * |g t₁| := by rw [abs_mul]
      _ ≤ |f t₁| + (|L| + ε / 2) * |g t₁| := by gcongr
  have hsmall : |(f t₁ - q * g t₁) / g x| < ε / 2 := by
    rw [abs_div, div_lt_iff₀ hgpos]
    rw [div_lt_iff₀ hε] at hgx
    linarith
  rw [Real.dist_eq, hsplit]
  calc |(q - L) + (f t₁ - q * g t₁) / g x| ≤ |q - L| + |(f t₁ - q * g t₁) / g x| :=
        abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hqL hsmall
    _ = ε := by ring

end Ch12.LHopital
