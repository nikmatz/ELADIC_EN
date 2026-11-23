-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 19 · Comparison Test — Limit Form · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch19.OriakoKritirio
open Filter Topology Asymptotics

theorem limit_comparison (a b : ℕ → ℝ) (L : ℝ) (hL : 0 < L) (hb : ∀ n, 0 < b n)
    (hlim : Tendsto (fun n => a n / b n) atTop (𝓝 L)) : Summable a ↔ Summable b := by
  -- a = O(b), because a/b → L
  have hab : a =O[atTop] b :=
    isBigO_of_div_tendsto_nhds (Eventually.of_forall fun n h0 => absurd h0 (hb n).ne') L hlim
  -- b = O(a), because b/a → 1/L
  have hba : b =O[atTop] a := by
    have hinv : Tendsto (fun n => b n / a n) atTop (𝓝 L⁻¹) := by
      refine (hlim.inv₀ hL.ne').congr' ?_
      filter_upwards with n
      exact inv_div (a n) (b n)
    refine isBigO_of_div_tendsto_nhds ?_ L⁻¹ hinv
    filter_upwards [hlim.eventually (lt_mem_nhds hL)] with n hn h0
    rw [h0, zero_div] at hn
    exact absurd hn (lt_irrefl 0)
  exact ⟨fun ha => summable_of_isBigO_nat' ha hba, fun hb' => summable_of_isBigO_nat' hb' hab⟩

end Ch19.OriakoKritirio
