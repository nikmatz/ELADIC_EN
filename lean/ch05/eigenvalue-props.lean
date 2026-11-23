-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 5 · Properties of Eigenvalues · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch5.IdiotitesIdiotimon
open Matrix

variable {n : ℕ}

theorem det_transpose_shift (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) :
    (Aᵀ - μ • 1).det = (A - μ • 1).det := by
  rw [← det_transpose (A - μ • 1), transpose_sub, transpose_smul, transpose_one]

theorem charpoly_of_transpose (A : Matrix (Fin n) (Fin n) ℝ) : Aᵀ.charpoly = A.charpoly :=
  charpoly_transpose A

theorem det_shift_triangular (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsUpperTriangular) (μ : ℝ) :
    (A - μ • 1).det = ∏ i, (A i i - μ) := by
  have h : (A - μ • 1).IsUpperTriangular := by
    intro i j hij
    have hne : i ≠ j := hij.ne'
    rw [Matrix.sub_apply, Matrix.smul_apply, one_apply_ne hne, smul_zero, sub_zero]
    exact hA hij
  rw [det_of_isUpperTriangular h]
  simp only [Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]

theorem eigen_triangular (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsUpperTriangular) (μ : ℝ) :
    (A - μ • 1).det = 0 ↔ ∃ i, A i i = μ := by
  rw [det_shift_triangular A hA μ, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, sub_eq_zero]

theorem pow_eig (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) (v : Fin n → ℝ) (h : A *ᵥ v = μ • v)
    (k : ℕ) : (A ^ k) *ᵥ v = (μ ^ k) • v := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, one_mulVec, one_smul]
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec]
    rw [h, mulVec_smul]
    rw [ih, smul_smul]
    rw [pow_succ']

theorem smul_eig (A : Matrix (Fin n) (Fin n) ℝ) (μ c : ℝ) (v : Fin n → ℝ) (h : A *ᵥ v = μ • v) :
    (c • A) *ᵥ v = (c * μ) • v := by
  rw [smul_mulVec, h, smul_smul]

theorem shift_eig (A : Matrix (Fin n) (Fin n) ℝ) (μ c : ℝ) (v : Fin n → ℝ) (h : A *ᵥ v = μ • v) :
    (A + c • 1) *ᵥ v = (μ + c) • v := by
  rw [add_mulVec, h, smul_mulVec, one_mulVec, add_smul]

theorem poly_eig (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) (v : Fin n → ℝ) (h : A *ᵥ v = μ • v)
    (p : Polynomial ℝ) : (Polynomial.aeval A p) *ᵥ v = (p.eval μ) • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, add_mulVec, hp, hq, Polynomial.eval_add, add_smul]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, smul_mulVec, pow_eig A μ v h k, smul_smul]

theorem inv_eig (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (μ : ℝ) (v : Fin n → ℝ)
    (hv : v ≠ 0) (h : A *ᵥ v = μ • v) : A⁻¹ *ᵥ v = μ⁻¹ • v := by
  have hμ : μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at h
    exact hA (exists_mulVec_eq_zero_iff.mp ⟨v, hv, h⟩)
  have h2 : A⁻¹ *ᵥ (A *ᵥ v) = v := by
    rw [mulVec_mulVec, nonsing_inv_mul A hA.isUnit, one_mulVec]
  rw [h, mulVec_smul] at h2
  have h3 : μ⁻¹ • (μ • (A⁻¹ *ᵥ v)) = μ⁻¹ • v := by
    rw [h2]
  rw [smul_smul, inv_mul_cancel₀ hμ, one_smul] at h3
  exact h3

end Ch5.IdiotitesIdiotimon
