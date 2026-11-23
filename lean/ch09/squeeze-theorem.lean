-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 9 · Squeeze Theorem · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch9.Parembolh
open Filter Topology

-- the book's definition: lim_{x→x₀} f(x) = L
def HasLim (f : ℝ → ℝ) (x₀ L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - x₀| → |x - x₀| < δ → |f x - L| < ε

theorem squeeze (f g h : ℝ → ℝ) (x₀ L δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hle : ∀ x, 0 < |x - x₀| → |x - x₀| < δ₀ → h x ≤ f x ∧ f x ≤ g x)
    (hh : HasLim h x₀ L) (hg : HasLim g x₀ L) : HasLim f x₀ L := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hh ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg ε hε
  refine ⟨min δ₀ (min δ₁ δ₂), lt_min hδ₀ (lt_min hδ₁ hδ₂), ?_⟩
  intro x hx hxδ
  have hx₀ : |x - x₀| < δ₀ := lt_of_lt_of_le hxδ (min_le_left _ _)
  have hx₁ : |x - x₀| < δ₁ := lt_of_lt_of_le hxδ ((min_le_right _ _).trans (min_le_left _ _))
  have hx₂ : |x - x₀| < δ₂ := lt_of_lt_of_le hxδ ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hhf, hfg⟩ := hle x hx hx₀
  have ha := h₁ x hx hx₁
  have hb := h₂ x hx hx₂
  rw [abs_sub_lt_iff] at ha hb ⊢
  constructor
  · linarith [hb.1]
  · linarith [ha.2]

theorem lim_of_bound (f : ℝ → ℝ) (x₀ L : ℝ) (hb : ∀ x, |f x - L| ≤ |x - x₀|) :
    HasLim f x₀ L := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro x _ hxδ
  exact lt_of_le_of_lt (hb x) hxδ

theorem squeeze_mathlib (f g h : ℝ → ℝ) (x₀ L : ℝ) (hh : Tendsto h (𝓝[≠] x₀) (𝓝 L))
    (hg : Tendsto g (𝓝[≠] x₀) (𝓝 L)) (hhf : ∀ᶠ x in 𝓝[≠] x₀, h x ≤ f x)
    (hfg : ∀ᶠ x in 𝓝[≠] x₀, f x ≤ g x) : Tendsto f (𝓝[≠] x₀) (𝓝 L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' hh hg hhf hfg

end Ch9.Parembolh
