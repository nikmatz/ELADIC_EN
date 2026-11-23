-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 0 · Parallel and Perpendicular Lines · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch0.Eutheies

theorem no_common_point (m₁ m₂ b₁ b₂ : ℝ) (hm : m₁ = m₂) (hb : b₁ ≠ b₂) :
    ¬ ∃ x : ℝ, m₁ * x + b₁ = m₂ * x + b₂ := by
  rintro ⟨x, hx⟩
  rw [hm] at hx
  exact hb (by linarith)

theorem common_point (m₁ m₂ b₁ b₂ : ℝ) (hm : m₁ ≠ m₂) :
    ∃ x : ℝ, m₁ * x + b₁ = m₂ * x + b₂ := by
  have hne : m₁ - m₂ ≠ 0 := sub_ne_zero.mpr hm
  refine ⟨(b₂ - b₁) / (m₁ - m₂), ?_⟩
  have key : (m₁ - m₂) * ((b₂ - b₁) / (m₁ - m₂)) = b₂ - b₁ := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hne]
  linear_combination key

theorem parallel_iff (m₁ m₂ b₁ b₂ : ℝ) :
    (¬ ∃ x : ℝ, m₁ * x + b₁ = m₂ * x + b₂) ↔ m₁ = m₂ ∧ b₁ ≠ b₂ := by
  constructor
  · intro h
    by_cases hm : m₁ = m₂
    · refine ⟨hm, ?_⟩
      intro hb
      apply h
      exact ⟨0, by rw [hm, hb]⟩
    · exact absurd (common_point m₁ m₂ b₁ b₂ hm) h
  · rintro ⟨hm, hb⟩
    exact no_common_point m₁ m₂ b₁ b₂ hm hb

theorem coincide (m b : ℝ) : ∀ x : ℝ, m * x + b = m * x + b := fun _ => rfl

theorem perpendicular_iff (m₁ m₂ : ℝ) : (1 : ℝ) * 1 + m₁ * m₂ = 0 ↔ m₁ * m₂ = -1 := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

end Ch0.Eutheies
