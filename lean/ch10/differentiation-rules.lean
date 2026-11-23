-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 10 · Rules of Differentiation · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch10.KanonesParagogisis

theorem d_const (x c : ℝ) : HasDerivAt (fun _ => c) 0 x := hasDerivAt_const x c

theorem d_pow (x : ℝ) (n : ℕ) : HasDerivAt (fun y => y ^ n) (n * x ^ (n - 1)) x :=
  hasDerivAt_pow n x

theorem d_exp (x : ℝ) : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x

theorem d_log (x : ℝ) (hx : x ≠ 0) : HasDerivAt Real.log (1 / x) x := by
  rw [one_div]
  exact Real.hasDerivAt_log hx

theorem d_sin (x : ℝ) : HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin x

theorem d_cos (x : ℝ) : HasDerivAt Real.cos (-Real.sin x) x := Real.hasDerivAt_cos x

theorem d_const_mul (f : ℝ → ℝ) (x f' c : ℝ) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => c * f y) (c * f') x := hf.const_mul c

theorem d_add (f g : ℝ → ℝ) (x f' g' : ℝ) (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y + g y) (f' + g') x := hf.add hg

theorem d_sub (f g : ℝ → ℝ) (x f' g' : ℝ) (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y - g y) (f' - g') x := hf.sub hg

theorem d_mul (f g : ℝ → ℝ) (x f' g' : ℝ) (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y * g y) (f' * g x + f x * g') x := hf.mul hg

theorem d_div (f g : ℝ → ℝ) (x f' g' : ℝ) (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (hgx : g x ≠ 0) :
    HasDerivAt (fun y => f y / g y) ((f' * g x - f x * g') / g x ^ 2) x := hf.div hg hgx

end Ch10.KanonesParagogisis
