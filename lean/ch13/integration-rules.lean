-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 13 · Basic Rules of Integration · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch13.KanonesOloklirwsis

-- ∫ (c₁ f + c₂ g) dx = c₁ ∫ f dx + c₂ ∫ g dx, written with antiderivatives
theorem linearity (F G f g : ℝ → ℝ) (c₁ c₂ : ℝ) (I : Set ℝ)
    (hF : ∀ x ∈ I, HasDerivAt F (f x) x) (hG : ∀ x ∈ I, HasDerivAt G (g x) x) :
    ∀ x ∈ I, HasDerivAt (fun x => c₁ * F x + c₂ * G x) (c₁ * f x + c₂ * g x) x := by
  intro x hx
  have h1 : HasDerivAt (fun x => c₁ * F x) (c₁ * f x) x := (hF x hx).const_mul c₁
  have h2 : HasDerivAt (fun x => c₂ * G x) (c₂ * g x) x := (hG x hx).const_mul c₂
  exact h1.add h2

theorem const_mul_rule (F f : ℝ → ℝ) (c : ℝ) (I : Set ℝ) (hF : ∀ x ∈ I, HasDerivAt F (f x) x) :
    ∀ x ∈ I, HasDerivAt (fun x => c * F x) (c * f x) x :=
  fun x hx => (hF x hx).const_mul c

theorem add_rule (F G f g : ℝ → ℝ) (I : Set ℝ)
    (hF : ∀ x ∈ I, HasDerivAt F (f x) x) (hG : ∀ x ∈ I, HasDerivAt G (g x) x) :
    ∀ x ∈ I, HasDerivAt (fun x => F x + G x) (f x + g x) x :=
  fun x hx => (hF x hx).add (hG x hx)

theorem sub_rule (F G f g : ℝ → ℝ) (I : Set ℝ)
    (hF : ∀ x ∈ I, HasDerivAt F (f x) x) (hG : ∀ x ∈ I, HasDerivAt G (g x) x) :
    ∀ x ∈ I, HasDerivAt (fun x => F x - G x) (f x - g x) x := by
  intro x hx
  exact (hF x hx).sub (hG x hx)

end Ch13.KanonesOloklirwsis
