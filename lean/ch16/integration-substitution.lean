-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 16 · Substitution — the General Form · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch16.Antikatastasi

-- if F' = f, then F(g(x)) is an antiderivative of f(g(x)) g'(x)
theorem substitution (F f g g' : ℝ → ℝ) (hF : ∀ u, HasDerivAt F (f u) u)
    (hg : ∀ x, HasDerivAt g (g' x) x) (x : ℝ) :
    HasDerivAt (fun x => F (g x)) (f (g x) * g' x) x := by
  -- F has derivative f(u) at the point u = g(x)
  have h1 := hF (g x)
  -- chain rule
  have h2 := h1.comp x (hg x)
  exact h2

theorem substitution_example (x : ℝ) :
    HasDerivAt (fun x => Real.sin (x ^ 2)) (Real.cos (x ^ 2) * (2 * x)) x :=
  substitution Real.sin Real.cos (fun x => x ^ 2) (fun x => 2 * x) Real.hasDerivAt_sin
    (fun x => by simpa using hasDerivAt_pow 2 x) x

end Ch16.Antikatastasi
