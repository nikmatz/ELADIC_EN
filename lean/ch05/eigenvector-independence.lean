-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 5 · Linear Independence of Eigenvectors · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch5.AnexartisiaIdiodianysmaton
open Matrix

variable {n : ℕ}

theorem eigenvectors_independent (A : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (μ : Fin k → ℝ)
    (hμ : Function.Injective μ) (v : Fin k → Fin n → ℝ)
    (hv : ∀ i, v i ≠ 0 ∧ A *ᵥ v i = μ i • v i) : LinearIndependent ℝ v := by
  apply Module.End.eigenvectors_linearIndependent' (toLin' A) μ hμ v
  intro i
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff, toLin'_apply]
  exact ⟨(hv i).2, (hv i).1⟩

theorem eigenspaces_independent (A : Matrix (Fin n) (Fin n) ℝ) {k : ℕ} (μ : Fin k → ℝ)
    (hμ : Function.Injective μ) :
    iSupIndep (fun i => Module.End.eigenspace (toLin' A) (μ i)) :=
  (Module.End.eigenspaces_iSupIndep (toLin' A)).comp hμ

end Ch5.AnexartisiaIdiodianysmaton
