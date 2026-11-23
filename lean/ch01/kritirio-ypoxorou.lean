-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Subspace Criterion · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.KritirioYpoxorou

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem zero_mem_of_closed (W : Set V) (hne : W.Nonempty)
    (h : ∀ u ∈ W, ∀ v ∈ W, ∀ a b : ℝ, a • u + b • v ∈ W) : (0 : V) ∈ W := by
  obtain ⟨w, hw⟩ := hne
  have h0 := h w hw w hw 0 0
  rw [zero_smul, zero_add] at h0
  exact h0

theorem add_mem_of_closed (W : Set V)
    (h : ∀ u ∈ W, ∀ v ∈ W, ∀ a b : ℝ, a • u + b • v ∈ W) {u v : V} (hu : u ∈ W) (hv : v ∈ W) :
    u + v ∈ W := by
  have h1 := h u hu v hv 1 1
  rw [one_smul, one_smul] at h1
  exact h1

theorem smul_mem_of_closed (W : Set V)
    (h : ∀ u ∈ W, ∀ v ∈ W, ∀ a b : ℝ, a • u + b • v ∈ W) (c : ℝ) {u : V} (hu : u ∈ W) :
    c • u ∈ W := by
  have h2 := h u hu u hu c 0
  rw [zero_smul, add_zero] at h2
  exact h2

/-- The subspace whose elements are exactly the elements of W. -/
def ofClosed (W : Set V) (hne : W.Nonempty)
    (h : ∀ u ∈ W, ∀ v ∈ W, ∀ a b : ℝ, a • u + b • v ∈ W) : Submodule ℝ V where
  carrier := W
  zero_mem' := zero_mem_of_closed W hne h
  add_mem' := add_mem_of_closed W h
  smul_mem' := smul_mem_of_closed W h

theorem closed (W : Submodule ℝ V) :
    (W : Set V).Nonempty ∧ ∀ u ∈ W, ∀ v ∈ W, ∀ a b : ℝ, a • u + b • v ∈ W := by
  refine ⟨⟨0, W.zero_mem⟩, ?_⟩
  intro u hu v hv a b
  exact W.add_mem (W.smul_mem a hu) (W.smul_mem b hv)

theorem criterion (W : Set V) :
    (∃ S : Submodule ℝ V, (S : Set V) = W) ↔
      W.Nonempty ∧ ∀ u ∈ W, ∀ v ∈ W, ∀ a b : ℝ, a • u + b • v ∈ W := by
  constructor
  · rintro ⟨S, rfl⟩
    exact closed S
  · rintro ⟨hne, h⟩
    exact ⟨ofClosed W hne h, rfl⟩

end Ch1.KritirioYpoxorou
