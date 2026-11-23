-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 5 · Spectral Decomposition of a Symmetric Matrix · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch5.FasmatikiApothesi
open Matrix

variable {n : ℕ}

-- the real matrix A, viewed as a complex matrix
def toC (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ := A.map Complex.ofReal

theorem toC_hermitian (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) : (toC A).IsHermitian := by
  have hH : A.IsHermitian := isHermitian_iff_isSymm.mpr hA
  exact hH.map Complex.ofReal (fun x => by rw [star_trivial, Complex.star_def, Complex.conj_ofReal])

theorem eig_mem_spectrum (M : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) (v : Fin n → ℂ) (hv : v ≠ 0)
    (h : M *ᵥ v = μ • v) : μ ∈ spectrum ℂ M := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    not_not]
  apply exists_mulVec_eq_zero_iff.mp
  refine ⟨v, hv, ?_⟩
  rw [sub_mulVec, smul_mulVec, one_mulVec, h, sub_self]

theorem real_eigenvalues (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (μ : ℂ) (v : Fin n → ℂ)
    (hv : v ≠ 0) (h : toC A *ᵥ v = μ • v) : μ.im = 0 := by
  have hmem := eig_mem_spectrum (toC A) μ v hv h
  rw [(toC_hermitian A hA).spectrum_eq_image_range] at hmem
  obtain ⟨r, -, rfl⟩ := hmem
  simp

theorem orthogonal_eigenvectors (A : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = A) (μ ν : ℝ)
    (v w : Fin n → ℝ) (hv : A *ᵥ v = μ • v) (hw : A *ᵥ w = ν • w) (hμν : μ ≠ ν) :
    v ⬝ᵥ w = 0 := by
  have h1 : (A *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (A *ᵥ w) := by
    rw [← vecMul_transpose, hA, ← dotProduct_mulVec]
  rw [hv, hw, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h1
  have h2 : (μ - ν) * (v ⬝ᵥ w) = 0 := by
    rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hμν
  · exact h3

end Ch5.FasmatikiApothesi
