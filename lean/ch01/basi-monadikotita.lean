-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Basis Theorem — Uniqueness of the Number of Elements · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.BasiMonadikotita
open Module

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem card_eq_dim {ι : Type*} [Fintype ι] (b : Basis ι ℝ V) :
    Fintype.card ι = finrank ℝ V :=
  (finrank_eq_card_basis b).symm

theorem same_card {ι κ : Type*} [Fintype ι] [Fintype κ] (b₁ : Basis ι ℝ V) (b₂ : Basis κ ℝ V) :
    Fintype.card ι = Fintype.card κ := by
  rw [card_eq_dim b₁, card_eq_dim b₂]

end Ch1.BasiMonadikotita
