-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 16 · Integration by Parts · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch16.KataParagontes

-- if G is an antiderivative of v u' (that is, G = ∫ v du), then u v - G is an antiderivative of u v'
theorem parts (u v u' v' G : ℝ → ℝ) (hu : ∀ x, HasDerivAt u (u' x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hG : ∀ x, HasDerivAt G (v x * u' x) x) (x : ℝ) :
    HasDerivAt (fun x => u x * v x - G x) (u x * v' x) x := by
  -- product rule: (u v)' = u' v + u v'
  have h1 : HasDerivAt (fun x => u x * v x) (u' x * v x + u x * v' x) x := (hu x).mul (hv x)
  -- we subtract G, which has derivative v u'
  have h2 : HasDerivAt (fun x => u x * v x - G x) (u' x * v x + u x * v' x - v x * u' x) x :=
    h1.sub (hG x)
  convert h2 using 1
  ring

theorem parts_example (x : ℝ) :
    HasDerivAt (fun x => x * Real.exp x - Real.exp x) (x * Real.exp x) x :=
  parts (fun x => x) Real.exp (fun _ => 1) Real.exp Real.exp hasDerivAt_id'
    Real.hasDerivAt_exp (fun x => by simpa using Real.hasDerivAt_exp x) x

end Ch16.KataParagontes
