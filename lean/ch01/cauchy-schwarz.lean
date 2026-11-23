-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Cauchy–Schwarz Inequality · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.CauchySchwarz
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem expand (u v : V) (t : ℝ) :
    ‖u + t • v‖ ^ 2 = ‖u‖ ^ 2 + 2 * (t * ⟪u, v⟫_ℝ) + t ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem sq_version (u v : V) : ⟪u, v⟫_ℝ ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  have h : ∀ t : ℝ, 0 ≤ ‖v‖ ^ 2 * (t * t) + 2 * ⟪u, v⟫_ℝ * t + ‖u‖ ^ 2 := by
    intro t
    have e := expand u v t
    have p := sq_nonneg ‖u + t • v‖
    nlinarith [e, p]
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith [hd]

theorem cauchy_schwarz (u v : V) : |⟪u, v⟫_ℝ| ≤ ‖u‖ * ‖v‖ := by
  apply abs_le_of_sq_le_sq _ (by positivity)
  rw [mul_pow]
  exact sq_version u v

theorem equality_iff (u v : V) :
    |⟪u, v⟫_ℝ| = ‖u‖ * ‖v‖ ↔ ¬ LinearIndependent ℝ ![u, v] := by
  by_cases hu : u = 0
  · subst hu
    simp only [inner_zero_left, abs_zero, norm_zero, zero_mul, true_iff]
    intro h
    exact h.ne_zero 0 rfl
  · have key := (norm_inner_eq_norm_tfae ℝ u v).out 1 3
    rw [← Real.norm_eq_abs, key, LinearIndependent.pair_iff' hu]
    simp only [hu, false_or, not_forall, not_not, ne_eq]
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨r, hr.symm⟩
    · rintro ⟨r, hr⟩
      exact ⟨r, hr.symm⟩

end Ch1.CauchySchwarz
