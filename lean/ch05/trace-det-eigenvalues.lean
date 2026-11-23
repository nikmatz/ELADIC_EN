-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 5 · Trace, Determinant and Eigenvalues · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch5.IxnosOrizousa
open Matrix

variable {n : ℕ}

theorem trace_sum_eigs (A : Matrix (Fin n) (Fin n) ℂ) : A.trace = A.charpoly.roots.sum :=
  trace_eq_sum_roots_charpoly A

theorem det_prod_eigs (A : Matrix (Fin n) (Fin n) ℂ) : A.det = A.charpoly.roots.prod :=
  det_eq_prod_roots_charpoly A

theorem card_eigs (A : Matrix (Fin n) (Fin n) ℂ) : Multiset.card A.charpoly.roots = n := by
  rw [IsAlgClosed.card_roots_eq_natDegree, charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem invertible_iff_no_zero (A : Matrix (Fin n) (Fin n) ℂ) :
    IsUnit A ↔ (0 : ℂ) ∉ A.charpoly.roots := by
  rw [isUnit_iff_isUnit_det, isUnit_iff_ne_zero, det_prod_eigs, Ne, Multiset.prod_eq_zero_iff]

end Ch5.IxnosOrizousa
