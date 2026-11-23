-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 1 · Basic Properties of a Vector Space · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

/-!
# Basic Properties of a Vector Space (Chapter 1)

We define a vector space as in the book: a set "V" with addition,
a zero vector, negatives and scalar multiplication by real numbers,
satisfying eight axioms. Every property below is proved from these
axioms alone.
("λ" is a reserved word in Lean, so we call the scalars "κ" and "μ".)
-/

/-- A (linear) vector space over ℝ, with the eight axioms of the book. -/
class VectorSpace (V : Type) extends Add V, Zero V, Neg V, SMul ℝ V where
  /-- u + v = v + u -/
  add_comm : ∀ u v : V, u + v = v + u
  /-- (u + v) + w = u + (v + w) -/
  add_assoc : ∀ u v w : V, u + v + w = u + (v + w)
  /-- u + 0 = u -/
  add_zero : ∀ u : V, u + 0 = u
  /-- u + (−u) = 0 -/
  add_neg : ∀ u : V, u + -u = 0
  /-- κ·(u + v) = κ·u + κ·v -/
  smul_add : ∀ (κ : ℝ) (u v : V), κ • (u + v) = κ • u + κ • v
  /-- (κ + μ)·u = κ·u + μ·u -/
  add_smul : ∀ (κ μ : ℝ) (u : V), (κ + μ) • u = κ • u + μ • u
  /-- (κμ)·u = κ·(μ·u) -/
  mul_smul : ∀ (κ μ : ℝ) (u : V), (κ * μ) • u = κ • (μ • u)
  /-- 1·u = u -/
  one_smul : ∀ u : V, (1 : ℝ) • u = u

namespace Ch1

variable {V : Type} [VectorSpace V]

/-- (1) The zero vector is unique. -/
theorem zero_unique (z : V) (hz : ∀ u : V, u + z = u) : z = 0 := by
  calc z = z + 0 := (VectorSpace.add_zero z).symm
    _ = 0 + z := VectorSpace.add_comm z 0
    _ = 0 := hz 0

/-- (2) The negative of every vector is unique. -/
theorem neg_unique {u w : V} (h : u + w = 0) : w = -u := by
  calc w = w + 0 := (VectorSpace.add_zero w).symm
    _ = w + (u + -u) := by rw [VectorSpace.add_neg]
    _ = w + u + -u := (VectorSpace.add_assoc w u (-u)).symm
    _ = u + w + -u := by rw [VectorSpace.add_comm w u]
    _ = 0 + -u := by rw [h]
    _ = -u + 0 := VectorSpace.add_comm 0 (-u)
    _ = -u := VectorSpace.add_zero (-u)

/-- Lemma: if x + x = x, then x = 0 (add −x to both sides). -/
theorem eq_zero_of_add_self {x : V} (h : x + x = x) : x = 0 := by
  calc x = x + 0 := (VectorSpace.add_zero x).symm
    _ = x + (x + -x) := by rw [VectorSpace.add_neg]
    _ = x + x + -x := (VectorSpace.add_assoc x x (-x)).symm
    _ = x + -x := by rw [h]
    _ = 0 := VectorSpace.add_neg x

/-- (3) 0·u = 0 -/
theorem zero_smul' (u : V) : (0 : ℝ) • u = 0 := by
  apply eq_zero_of_add_self
  rw [← VectorSpace.add_smul]
  rw [add_zero]

/-- (4) κ·0 = 0 -/
theorem smul_zero' (κ : ℝ) : κ • (0 : V) = 0 := by
  apply eq_zero_of_add_self
  rw [← VectorSpace.smul_add]
  rw [VectorSpace.add_zero]

/-- (5) (−1)·u = −u -/
theorem neg_one_smul' (u : V) : (-1 : ℝ) • u = -u := by
  apply neg_unique
  calc u + (-1 : ℝ) • u = (1 : ℝ) • u + (-1 : ℝ) • u := by rw [VectorSpace.one_smul]
    _ = ((1 : ℝ) + -1) • u := (VectorSpace.add_smul 1 (-1) u).symm
    _ = (0 : ℝ) • u := by norm_num
    _ = 0 := zero_smul' u

/-- (6) If κ·u = 0, then κ = 0 or u = 0. -/
theorem eq_zero_or_eq_zero_of_smul_eq_zero {κ : ℝ} {u : V} (h : κ • u = 0) :
    κ = 0 ∨ u = 0 := by
  by_cases hκ : κ = 0
  · left
    exact hκ
  · right
    calc u = (1 : ℝ) • u := (VectorSpace.one_smul u).symm
      _ = (κ⁻¹ * κ) • u := by rw [inv_mul_cancel₀ hκ]
      _ = κ⁻¹ • (κ • u) := VectorSpace.mul_smul κ⁻¹ κ u
      _ = κ⁻¹ • (0 : V) := by rw [h]
      _ = 0 := smul_zero' κ⁻¹

end Ch1

/-! ## The same properties are ready-made in Mathlib (there a vector space is called a "Module") -/
section InMathlib
variable {W : Type} [AddCommGroup W] [Module ℝ W]

example (u : W) : (0 : ℝ) • u = 0 := zero_smul ℝ u
example (κ : ℝ) : κ • (0 : W) = 0 := smul_zero κ
example (u : W) : (-1 : ℝ) • u = -u := neg_one_smul ℝ u
example (κ : ℝ) (u : W) : κ • u = 0 ↔ κ = 0 ∨ u = 0 := smul_eq_zero
end InMathlib
