-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 0 · Fundamental Theorem of Algebra · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch0.ThemeliodesAlgebras
open Polynomial

theorem has_root (f : ℂ[X]) (hf : 0 < f.natDegree) : ∃ z : ℂ, f.IsRoot z :=
  Complex.exists_root (natDegree_pos_iff_degree_pos.mp hf)

theorem n_roots (f : ℂ[X]) : Multiset.card f.roots = f.natDegree :=
  IsAlgClosed.card_roots_eq_natDegree

end Ch0.ThemeliodesAlgebras
