-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 3 · Kronecker–Capelli Theorem · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch3.KroneckerCapelli
open Matrix Module Submodule

variable {m n : ℕ}

/-- The augmented matrix [A | b]: the columns of A, followed by b as the last column. -/
def augmented (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Matrix (Fin m) (Fin (n + 1)) ℝ :=
  Matrix.of fun i => Fin.snoc (A i) (b i)

theorem cols_augmented (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Set.range (augmented A b).col = insert b (Set.range A.col) := by
  ext v
  simp only [Set.mem_range, Set.mem_insert_iff]
  constructor
  · rintro ⟨j, rfl⟩
    induction j using Fin.lastCases with
    | last => left; funext i; simp [augmented]
    | cast k => right; exact ⟨k, by funext i; simp [augmented]⟩
  · rintro (rfl | ⟨k, rfl⟩)
    · exact ⟨Fin.last n, by funext i; simp [augmented]⟩
    · exact ⟨k.castSucc, by funext i; simp [augmented]⟩

theorem solvable_iff_mem (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x, A *ᵥ x = b) ↔ b ∈ span ℝ (Set.range A.col) := by
  rw [← range_mulVecLin, LinearMap.mem_range]
  rfl

theorem compatible_iff (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x, A *ᵥ x = b) ↔ A.rank = (augmented A b).rank := by
  rw [solvable_iff_mem]
  rw [← finrank_span_range_col, ← finrank_span_range_col]
  rw [cols_augmented]
  constructor
  · intro hb
    rw [span_insert_eq_span hb]
  · intro h
    have hle : span ℝ (Set.range A.col) ≤ span ℝ (insert b (Set.range A.col)) :=
      span_mono (Set.subset_insert b _)
    have heq := eq_of_le_of_finrank_eq hle h
    rw [heq]
    exact subset_span (Set.mem_insert b _)

theorem dim_solutions (A : Matrix (Fin m) (Fin n) ℝ) :
    finrank ℝ (LinearMap.ker A.mulVecLin) = n - A.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [finrank_range_mulVecLin, finrank_fin_fun] at h
  omega

theorem unique_of_rank (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (h : A.rank = n)
    (x y : Fin n → ℝ) (hx : A *ᵥ x = b) (hy : A *ᵥ y = b) : x = y := by
  have hk : LinearMap.ker A.mulVecLin = ⊥ := by
    rw [← Submodule.finrank_eq_zero, dim_solutions, h, Nat.sub_self]
  have hmem : x - y ∈ LinearMap.ker A.mulVecLin := by
    rw [LinearMap.mem_ker, mulVecLin_apply, mulVec_sub, hx, hy, sub_self]
  rw [hk, Submodule.mem_bot] at hmem
  exact sub_eq_zero.mp hmem

end Ch3.KroneckerCapelli
