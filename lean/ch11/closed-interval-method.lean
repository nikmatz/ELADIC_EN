-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 11 · The Closed Interval Method · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch11.KleistoDiastima

theorem max_at_critical_or_endpoint (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ M ∈ Set.Icc a b, (∀ x ∈ Set.Icc a b, f x ≤ f M) ∧
      (M = a ∨ M = b ∨ ∀ f', HasDerivAt f f' M → f' = 0) := by
  obtain ⟨M, hM, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab) hf
  refine ⟨M, hM, fun x hx => isMaxOn_iff.mp hmax x hx, ?_⟩
  by_cases ha : M = a
  · exact Or.inl ha
  by_cases hb : M = b
  · exact Or.inr (Or.inl hb)
  refine Or.inr (Or.inr ?_)
  intro f' hf'
  have hMi : M ∈ Set.Ioo a b := ⟨lt_of_le_of_ne hM.1 (Ne.symm ha), lt_of_le_of_ne hM.2 hb⟩
  have hloc : IsLocalMax f M := hmax.isLocalMax (Icc_mem_nhds hMi.1 hMi.2)
  exact hloc.hasDerivAt_eq_zero hf'

theorem min_at_critical_or_endpoint (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ m ∈ Set.Icc a b, (∀ x ∈ Set.Icc a b, f m ≤ f x) ∧
      (m = a ∨ m = b ∨ ∀ f', HasDerivAt f f' m → f' = 0) := by
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hab) hf
  refine ⟨m, hm, fun x hx => isMinOn_iff.mp hmin x hx, ?_⟩
  by_cases ha : m = a
  · exact Or.inl ha
  by_cases hb : m = b
  · exact Or.inr (Or.inl hb)
  refine Or.inr (Or.inr ?_)
  intro f' hf'
  have hmi : m ∈ Set.Ioo a b := ⟨lt_of_le_of_ne hm.1 (Ne.symm ha), lt_of_le_of_ne hm.2 hb⟩
  have hloc : IsLocalMin f m := hmin.isLocalMin (Icc_mem_nhds hmi.1 hmi.2)
  exact hloc.hasDerivAt_eq_zero hf'

theorem max_at_endpoint (f f' : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hd : ∀ x, HasDerivAt f (f' x) x)
    (hne : ∀ x, f' x ≠ 0) :
    ∃ M ∈ Set.Icc a b, (∀ x ∈ Set.Icc a b, f x ≤ f M) ∧ (M = a ∨ M = b) := by
  obtain ⟨M, hM, hmax, h⟩ := max_at_critical_or_endpoint f a b hab hf
  rcases h with h | h | h
  · exact ⟨M, hM, hmax, Or.inl h⟩
  · exact ⟨M, hM, hmax, Or.inr h⟩
  · exact absurd (h (f' M) (hd M)) (hne M)

end Ch11.KleistoDiastima
