-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 0 · nth Roots of a Complex Number · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch0.NostesRizes
open Complex
open scoped Real

/-- The root with index k: ρ^(1/n) · e^(i(φ + 2kπ)/n). -/
noncomputable def z (ρ φ : ℝ) (n k : ℕ) : ℂ :=
  ((ρ ^ ((n : ℝ)⁻¹) : ℝ) : ℂ) * exp ((φ + 2 * k * π) / n * I)

theorem z_pow (ρ φ : ℝ) (hρ : 0 < ρ) (n k : ℕ) (hn : n ≠ 0) :
    z ρ φ n k ^ n = ρ * exp (φ * I) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  unfold z
  rw [mul_pow, ← ofReal_pow, Real.rpow_inv_natCast_pow hρ.le hn]
  rw [← exp_natCast_mul]
  have h : (n : ℂ) * ((φ + 2 * k * π) / n * I) = φ * I + k * (2 * π * I) := by
    calc (n : ℂ) * ((φ + 2 * k * π) / n * I) = (n / n) * ((φ + 2 * k * π) * I) := by ring
      _ = φ * I + k * (2 * π * I) := by rw [div_self hn', one_mul]; ring
  rw [h, exp_add, exp_nat_mul_two_pi_mul_I, mul_one]

theorem z_eq (ρ φ : ℝ) (n k : ℕ) :
    z ρ φ n k = z ρ φ n 0 * exp (2 * π * I / n) ^ k := by
  unfold z
  rw [← exp_natCast_mul, mul_assoc (((ρ ^ ((n : ℝ)⁻¹) : ℝ) : ℂ)), ← exp_add]
  congr 2
  push_cast
  ring

theorem z_injective (ρ φ : ℝ) (hρ : 0 < ρ) (n : ℕ) (hn : n ≠ 0) {j k : ℕ}
    (hj : j < n) (hk : k < n) (h : z ρ φ n j = z ρ φ n k) : j = k := by
  have h0 : z ρ φ n 0 ≠ 0 := by
    unfold z
    apply mul_ne_zero
    · exact_mod_cast (Real.rpow_pos_of_pos hρ _).ne'
    · exact exp_ne_zero _
  rw [z_eq ρ φ n j, z_eq ρ φ n k] at h
  have h' := mul_left_cancel₀ h0 h
  exact (isPrimitiveRoot_exp n hn).pow_inj hj hk h'

theorem exactly_n (n : ℕ) (hn : n ≠ 0) (w : ℂ) (hw : w ≠ 0) :
    (Polynomial.nthRoots n w).Nodup ∧ Multiset.card (Polynomial.nthRoots n w) = n := by
  have hζ := isPrimitiveRoot_exp n hn
  refine ⟨hζ.nthRoots_nodup hw, ?_⟩
  have hex : ∃ α, α ^ n = w := IsAlgClosed.exists_pow_nat_eq w (Nat.pos_of_ne_zero hn)
  rw [hζ.card_nthRoots]
  simp [hex]

theorem all_roots (ρ φ : ℝ) (hρ : 0 < ρ) (n : ℕ) (hn : n ≠ 0) (x : ℂ)
    (hx : x ^ n = ρ * exp (φ * I)) : ∃ k < n, x = z ρ φ n k := by
  have hζ := isPrimitiveRoot_exp n hn
  have hmem : x ∈ Polynomial.nthRoots n ((ρ : ℂ) * exp (φ * I)) :=
    (Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hn)).mpr hx
  rw [hζ.nthRoots_eq (z_pow ρ φ hρ n 0 hn)] at hmem
  obtain ⟨k, hk, hkx⟩ := Multiset.mem_map.mp hmem
  refine ⟨k, Multiset.mem_range.mp hk, ?_⟩
  rw [← hkx, z_eq ρ φ n k, mul_comm]

end Ch0.NostesRizes
