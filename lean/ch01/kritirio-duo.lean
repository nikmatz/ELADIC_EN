-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Linear Dependence Test for Two Vectors · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch1.KritirioDuo

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem dependent_of_multiple (u v : V) (c : ℝ) (h : u = c • v) :
    ¬ LinearIndependent ℝ ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro hli
  have h1 := hli 1 (-c) (by rw [h]; module)
  norm_num at h1

theorem dependent_of_multiple' (u v : V) (c : ℝ) (h : v = c • u) :
    ¬ LinearIndependent ℝ ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro hli
  have h1 := hli (-c) 1 (by rw [h]; module)
  norm_num at h1

theorem multiple_of_dependent (u v : V) (h : ¬ LinearIndependent ℝ ![u, v]) :
    (∃ c : ℝ, u = c • v) ∨ (∃ c : ℝ, v = c • u) := by
  rw [LinearIndependent.pair_iff] at h
  push Not at h
  obtain ⟨s, t, hst, hne⟩ := h
  by_cases hs : s = 0
  · right
    refine ⟨0, ?_⟩
    rw [hs, zero_smul, zero_add] at hst
    rw [zero_smul]
    exact (smul_eq_zero.mp hst).resolve_left (hne hs)
  · left
    refine ⟨-t / s, ?_⟩
    have e : s • u = -(t • v) := eq_neg_of_add_eq_zero_left hst
    calc u = s⁻¹ • (s • u) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
      _ = s⁻¹ • -(t • v) := by rw [e]
      _ = (-t / s) • v := by rw [smul_neg, smul_smul, ← neg_smul]; congr 1; ring

theorem dependent_iff (u v : V) :
    ¬ LinearIndependent ℝ ![u, v] ↔ (∃ c : ℝ, u = c • v) ∨ (∃ c : ℝ, v = c • u) := by
  constructor
  · exact multiple_of_dependent u v
  · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
    · exact dependent_of_multiple u v c hc
    · exact dependent_of_multiple' u v c hc

end Ch1.KritirioDuo
