-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 0 · General Solution of the Basic Trigonometric Equations · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch0.TrigExisoseis
open Real

theorem sin_solutions (x k : ℝ) (hk : |k| ≤ 1) :
    sin x = k ↔ ∃ n : ℤ, x = arcsin k + 2 * n * π ∨ x = π - arcsin k + 2 * n * π := by
  have hs : sin (arcsin k) = k := sin_arcsin (abs_le.mp hk).1 (abs_le.mp hk).2
  constructor
  · intro h
    have e : sin (arcsin k) = sin x := by rw [hs, h]
    obtain ⟨n, hn⟩ := sin_eq_sin_iff.mp e
    refine ⟨n, ?_⟩
    rcases hn with hn | hn
    · left
      linarith
    · right
      linarith
  · rintro ⟨n, hn | hn⟩
    · have e : sin (arcsin k) = sin x := sin_eq_sin_iff.mpr ⟨n, Or.inl (by linarith)⟩
      rw [← e, hs]
    · have e : sin (arcsin k) = sin x := sin_eq_sin_iff.mpr ⟨n, Or.inr (by linarith)⟩
      rw [← e, hs]

theorem cos_solutions (x k : ℝ) (hk : |k| ≤ 1) :
    cos x = k ↔ ∃ n : ℤ, x = arccos k + 2 * n * π ∨ x = -arccos k + 2 * n * π := by
  have hc : cos (arccos k) = k := cos_arccos (abs_le.mp hk).1 (abs_le.mp hk).2
  constructor
  · intro h
    have e : cos (arccos k) = cos x := by rw [hc, h]
    obtain ⟨n, hn⟩ := cos_eq_cos_iff.mp e
    refine ⟨n, ?_⟩
    rcases hn with hn | hn
    · left
      linarith
    · right
      linarith
  · rintro ⟨n, hn | hn⟩
    · have e : cos (arccos k) = cos x := cos_eq_cos_iff.mpr ⟨n, Or.inl (by linarith)⟩
      rw [← e, hc]
    · have e : cos (arccos k) = cos x := cos_eq_cos_iff.mpr ⟨n, Or.inr (by linarith)⟩
      rw [← e, hc]

theorem tan_solutions (x k : ℝ) (hx : cos x ≠ 0) (h : tan x = k) :
    ∃ n : ℤ, x = arctan k + n * π := by
  have hc : 0 < cos (arctan k) := cos_arctan_pos k
  have h₁ : sin x = k * cos x := by
    rw [← h, tan_eq_sin_div_cos, div_mul_cancel₀ _ hx]
  have h₂ : sin (arctan k) = k * cos (arctan k) := by
    have t := tan_arctan k
    rw [tan_eq_sin_div_cos] at t
    have e := div_mul_cancel₀ (sin (arctan k)) hc.ne'
    rw [t] at e
    exact e.symm
  have h₃ : sin (x - arctan k) = 0 := by
    rw [sin_sub, h₁, h₂]
    ring
  obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp h₃
  exact ⟨n, by linarith⟩

theorem no_solution (x k : ℝ) (hk : 1 < |k|) : sin x ≠ k ∧ cos x ≠ k := by
  constructor
  · intro h
    have b := abs_sin_le_one x
    rw [h] at b
    linarith
  · intro h
    have b := abs_cos_le_one x
    rw [h] at b
    linarith

end Ch0.TrigExisoseis
