-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 4 · Matrix Representation of a Linear Transformation · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch4.AnaparastasiPinaka
open Matrix

variable {m n : ℕ}

theorem unique_matrix (A B : Matrix (Fin m) (Fin n) ℝ) (h : ∀ x, A *ᵥ x = B *ᵥ x) : A = B := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [toLin'_apply, toLin'_apply]
  exact h x

theorem matrix_of_linear (T : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    ∃! A : Matrix (Fin m) (Fin n) ℝ, ∀ x, T x = A *ᵥ x := by
  apply ExistsUnique.intro (LinearMap.toMatrix' T)
  · intro x
    rw [LinearMap.toMatrix'_mulVec]
  · intro B hB
    apply unique_matrix
    intro x
    rw [← hB x, LinearMap.toMatrix'_mulVec]

theorem columns_are_images (T : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (j : Fin n) :
    (LinearMap.toMatrix' T).col j = T (Pi.single j 1) := by
  rw [← mulVec_single_one, LinearMap.toMatrix'_mulVec]

end Ch4.AnaparastasiPinaka
