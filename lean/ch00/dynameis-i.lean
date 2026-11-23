-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 0 · Powers of i · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch0.DynameisI
open Complex

theorem pow_zero_I : I ^ 0 = 1 := pow_zero I

theorem pow_one_I : I ^ 1 = I := pow_one I

theorem pow_two_I : I ^ 2 = -1 := I_sq

theorem pow_three_I : I ^ 3 = -I := by
  rw [pow_succ, I_sq]
  ring

theorem pow_four_I : I ^ 4 = 1 := by
  rw [pow_succ, pow_three_I]
  rw [neg_mul, ← sq, I_sq, neg_neg]

theorem pow_mod_four (n : ℕ) : I ^ n = I ^ (n % 4) := by
  have h : n = 4 * (n / 4) + n % 4 := (Nat.div_add_mod n 4).symm
  conv_lhs => rw [h]
  rw [pow_add]
  rw [pow_mul]
  rw [pow_four_I]
  rw [one_pow, one_mul]

end Ch0.DynameisI
