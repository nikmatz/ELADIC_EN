-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 0 · ℂ as a Vector Space over ℝ · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch0.DianysmatikosC
open Complex

theorem dimension : Module.finrank ℝ ℂ = 2 := finrank_real_complex

theorem basis_one_I : ⇑basisOneI = ![1, I] := coe_basisOneI

theorem unique_repr (z : ℂ) : ∃! p : ℝ × ℝ, (p.1 : ℂ) * 1 + p.2 * I = z := by
  refine ⟨(z.re, z.im), ?_, ?_⟩
  · simp
  · rintro ⟨a, b⟩ h
    subst h
    simp

end Ch0.DianysmatikosC
