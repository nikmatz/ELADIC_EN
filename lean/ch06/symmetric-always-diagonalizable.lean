-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 6 · Symmetric Matrices: Always Orthogonally Diagonalizable · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch6.SymmetrikosDiagonopoiisimos
open Matrix Module

-- the general form: a symmetric operator on an inner product space
theorem geom_eq_alg_operator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) {m : ℕ}
    (hm : finrank ℝ E = m) (μ : ℝ) :
    finrank ℝ (End.eigenspace T μ) = T.charpoly.rootMultiplicity μ := by
  rw [← Polynomial.count_roots, hT.roots_charpoly_eq_eigenvalues hm, Multiset.count_map,
    ← hT.card_filter_eigenvalues_eq hm μ, Finset.card_def, Finset.filter_val]
  congr 1
  apply Multiset.filter_congr
  intro i _
  rw [Function.comp_apply, eq_comm]

variable {n : ℕ}

theorem charpoly_euclidean (A : Matrix (Fin n) (Fin n) ℝ) :
    (toEuclideanLin A).charpoly = A.charpoly := by
  rw [toEuclideanLin_eq_toLin_orthonormal, charpoly_toLin]

theorem geom_eq_alg (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (μ : ℝ) :
    finrank ℝ (End.eigenspace (toEuclideanLin A) μ) = A.charpoly.rootMultiplicity μ := by
  rw [← charpoly_euclidean A]
  exact geom_eq_alg_operator _ (isSymmetric_toEuclideanLin_iff.mpr hA) finrank_euclideanSpace μ

theorem orthogonal_diagonalization (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ, Qᵀ * Q = 1 ∧ A = Q * diagonal hA.eigenvalues * Qᵀ := by
  refine ⟨hA.eigenvectorUnitary, ?_, ?_⟩
  · rw [← conjTranspose_eq_transpose_of_trivial, ← star_eq_conjTranspose]
    exact Unitary.coe_star_mul_self hA.eigenvectorUnitary
  · conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
      conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.id_comp]

end Ch6.SymmetrikosDiagonopoiisimos
