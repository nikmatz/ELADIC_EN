-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 4 · One-to-One Transformations and the Kernel · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch4.EnaProsEnaPyrinas

variable {m n : ℕ}

theorem injective_iff_ker (T : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    Function.Injective T ↔ LinearMap.ker T = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    apply h
    rw [hx, map_zero]
  · intro h x y hxy
    have hsub : x - y ∈ LinearMap.ker T := by
      rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
    rw [h, Submodule.mem_bot, sub_eq_zero] at hsub
    exact hsub

theorem zero_of_injective (T : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (h : Function.Injective T)
    (x : Fin n → ℝ) (hx : T x = 0) : x = 0 := by
  apply h
  rw [hx, map_zero]

theorem mathlib_version (T : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    LinearMap.ker T = ⊥ ↔ Function.Injective T :=
  LinearMap.ker_eq_bot

end Ch4.EnaProsEnaPyrinas
