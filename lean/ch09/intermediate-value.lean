-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 9 · Intermediate Value Theorem (IVT) · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch9.EndiamesiTimi

theorem intermediate_value (f : ℝ → ℝ) (a b k : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hk : k ∈ Set.uIcc (f a) (f b)) :
    ∃ c ∈ Set.Icc a b, f c = k := by
  rw [← Set.uIcc_of_le hab] at hf ⊢
  exact intermediate_value_uIcc hf hk

theorem bolzano (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (hsign : f a * f b < 0) : ∃ c ∈ Set.Ioo a b, f c = 0 := by
  rcases mul_neg_iff.mp hsign with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact intermediate_value_Ioo' hab.le hf ⟨hb, ha⟩
  · exact intermediate_value_Ioo hab.le hf ⟨ha, hb⟩

end Ch9.EndiamesiTimi
