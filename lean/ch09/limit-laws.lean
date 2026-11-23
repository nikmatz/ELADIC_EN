-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 9 · Limit Laws · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch9.NomoiOrion
open Filter Topology

-- the book’s definition: lim_{x→x₀} f(x) = L
def HasLim (f : ℝ → ℝ) (x₀ L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - x₀| → |x - x₀| < δ → |f x - L| < ε

theorem lim_add (f g : ℝ → ℝ) (x₀ L M : ℝ) (hf : HasLim f x₀ L) (hg : HasLim g x₀ M) :
    HasLim (f + g) x₀ (L + M) := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg (ε / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro x hx hxδ
  have hfx := h₁ x hx (lt_of_lt_of_le hxδ (min_le_left δ₁ δ₂))
  have hgx := h₂ x hx (lt_of_lt_of_le hxδ (min_le_right δ₁ δ₂))
  rw [Pi.add_apply]
  calc |f x + g x - (L + M)| = |(f x - L) + (g x - M)| := by congr 1; ring
    _ ≤ |f x - L| + |g x - M| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfx hgx
    _ = ε := by ring

theorem lim_const (c x₀ : ℝ) : HasLim (fun _ => c) x₀ c := by
  intro ε hε
  refine ⟨1, one_pos, ?_⟩
  intro x _ _
  simpa using hε

-- the book’s definition agrees with the Mathlib limit
theorem hasLim_iff (f : ℝ → ℝ) (x₀ L : ℝ) : HasLim f x₀ L ↔ Tendsto f (𝓝[≠] x₀) (𝓝 L) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hx⟩ := h ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x hx1 hx2
    rw [Real.dist_eq] at hx2 ⊢
    exact hx x (abs_pos.mpr (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hx1))) hx2
  · intro h ε hε
    obtain ⟨δ, hδ, hx⟩ := h ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x hx1 hx2
    have hne : x ≠ x₀ := sub_ne_zero.mp (abs_pos.mp hx1)
    have h2 := hx (Set.mem_compl_singleton_iff.mpr hne) (by rw [Real.dist_eq]; exact hx2)
    rwa [Real.dist_eq] at h2

theorem lim_sub (f g : ℝ → ℝ) (x₀ L M : ℝ) (hf : HasLim f x₀ L) (hg : HasLim g x₀ M) :
    HasLim (f - g) x₀ (L - M) := by
  rw [hasLim_iff] at hf hg ⊢
  exact hf.sub hg

theorem lim_mul (f g : ℝ → ℝ) (x₀ L M : ℝ) (hf : HasLim f x₀ L) (hg : HasLim g x₀ M) :
    HasLim (f * g) x₀ (L * M) := by
  rw [hasLim_iff] at hf hg ⊢
  exact hf.mul hg

theorem lim_div (f g : ℝ → ℝ) (x₀ L M : ℝ) (hf : HasLim f x₀ L) (hg : HasLim g x₀ M)
    (hM : M ≠ 0) : HasLim (f / g) x₀ (L / M) := by
  rw [hasLim_iff] at hf hg ⊢
  exact hf.div hg hM

theorem lim_pow (f : ℝ → ℝ) (x₀ L : ℝ) (n : ℕ) (hf : HasLim f x₀ L) :
    HasLim (f ^ n) x₀ (L ^ n) := by
  rw [hasLim_iff] at hf ⊢
  exact hf.pow n

theorem lim_sqrt (f : ℝ → ℝ) (x₀ L : ℝ) (hf : HasLim f x₀ L) :
    HasLim (fun x => √(f x)) x₀ (√L) := by
  rw [hasLim_iff] at hf ⊢
  exact hf.sqrt

theorem lim_root (f : ℝ → ℝ) (x₀ L : ℝ) (n : ℕ) (hf : HasLim f x₀ L) :
    HasLim (fun x => f x ^ ((1 : ℝ) / n)) x₀ (L ^ ((1 : ℝ) / n)) := by
  rw [hasLim_iff] at hf ⊢
  exact hf.rpow_const (Or.inr (by positivity))

end Ch9.NomoiOrion
