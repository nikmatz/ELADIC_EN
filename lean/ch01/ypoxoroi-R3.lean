-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Geometric Subspaces of ℝ³ · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.YpoxoroiR3
open Module Submodule

theorem dim_le_three (W : Submodule ℝ (Fin 3 → ℝ)) : finrank ℝ W ≤ 3 := by
  have h := W.finrank_le
  rw [Module.finrank_fin_fun] at h
  exact h

theorem dim_zero_iff (W : Submodule ℝ (Fin 3 → ℝ)) : finrank ℝ W = 0 ↔ W = ⊥ :=
  Submodule.finrank_eq_zero

theorem dim_three_iff (W : Submodule ℝ (Fin 3 → ℝ)) : finrank ℝ W = 3 ↔ W = ⊤ := by
  constructor
  · intro h
    apply eq_top_of_finrank_eq
    rw [h, Module.finrank_fin_fun]
  · rintro rfl
    rw [finrank_top, Module.finrank_fin_fun]

theorem dim_one_iff (W : Submodule ℝ (Fin 3 → ℝ)) :
    finrank ℝ W = 1 ↔ ∃ v ≠ 0, W = span ℝ {v} := by
  constructor
  · intro h
    obtain ⟨v, hv, hall⟩ := finrank_eq_one_iff'.mp h
    refine ⟨v, fun h0 => hv (Subtype.ext h0), ?_⟩
    apply le_antisymm
    · intro x hx
      obtain ⟨c, hc⟩ := hall ⟨x, hx⟩
      rw [mem_span_singleton]
      exact ⟨c, congrArg Subtype.val hc⟩
    · rw [span_le, Set.singleton_subset_iff]
      exact v.2
  · rintro ⟨v, hv, rfl⟩
    exact finrank_span_singleton hv

theorem dim_two_iff (W : Submodule ℝ (Fin 3 → ℝ)) :
    finrank ℝ W = 2 ↔
      ∃ u v : Fin 3 → ℝ, LinearIndependent ℝ ![u, v] ∧ W = span ℝ (Set.range ![u, v]) := by
  constructor
  · intro h
    let b := Module.finBasisOfFinrankEq ℝ W h
    have hf : (W.subtype ∘ b) = ![(b 0 : Fin 3 → ℝ), (b 1 : Fin 3 → ℝ)] := by
      funext i
      fin_cases i <;> rfl
    refine ⟨b 0, b 1, ?_, ?_⟩
    · rw [← hf]
      exact b.linearIndependent.map' W.subtype (ker_subtype W)
    · rw [← hf, Set.range_comp, ← map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  · rintro ⟨u, v, h, rfl⟩
    rw [finrank_span_eq_card h, Fintype.card_fin]

theorem classification (W : Submodule ℝ (Fin 3 → ℝ)) :
    W = ⊥ ∨ (∃ v ≠ 0, W = span ℝ {v}) ∨
      (∃ u v : Fin 3 → ℝ, LinearIndependent ℝ ![u, v] ∧ W = span ℝ (Set.range ![u, v])) ∨
        W = ⊤ := by
  obtain h0 | h1 | h2 | h3 :
      finrank ℝ W = 0 ∨ finrank ℝ W = 1 ∨ finrank ℝ W = 2 ∨ finrank ℝ W = 3 := by
    have h := dim_le_three W
    omega
  · exact Or.inl ((dim_zero_iff W).mp h0)
  · exact Or.inr (Or.inl ((dim_one_iff W).mp h1))
  · exact Or.inr (Or.inr (Or.inl ((dim_two_iff W).mp h2)))
  · exact Or.inr (Or.inr (Or.inr ((dim_three_iff W).mp h3)))

end Ch1.YpoxoroiR3
