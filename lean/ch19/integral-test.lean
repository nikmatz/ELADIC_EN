-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 19 · Integral Test · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch19.KritirioOloklirwmatos
open MeasureTheory Filter Topology

-- f decreasing and nonnegative on [1, +∞): the series f(1) + f(2) + … is written Σ f(n + 1)
theorem integral_test (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (h0 : ∀ x ∈ Set.Ici (1 : ℝ), 0 ≤ f x) :
    Summable (fun n : ℕ => f (n + 1)) ↔ IntegrableOn f (Set.Ioi 1) := by
  have hf' : AntitoneOn f (Set.Ici ((1 : ℕ) : ℝ)) := by simpa using hf
  have h0' : ∀ t ∈ Set.Ioi ((1 : ℕ) : ℝ), 0 ≤ f t := fun t ht => by
    simp only [Nat.cast_one, Set.mem_Ioi] at ht
    exact h0 t (Set.mem_Ici.mpr ht.le)
  constructor
  · intro hs
    have h := hf'.integrableOn_Ioi_of_summable_comp_add (by simpa using hs) h0'
    simpa using h
  · intro hi
    have h := hf'.summable_of_integrableOn_Ioi (by simpa using hi) h0'
    have h2 := (summable_nat_add_iff 1).mpr h
    simpa using h2

-- bounds with the partial sums: ∫ from 1 to 1 + N ≤ f(1) + … + f(N)
theorem integral_le_partial_sum (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1)) (N : ℕ) :
    ∫ x in (1 : ℝ)..1 + N, f x ≤ ∑ i ∈ Finset.range N, f (1 + i) :=
  (hf.mono Set.Icc_subset_Ici_self).integral_le_sum

-- and f(2) + … + f(N + 1) ≤ ∫ from 1 to 1 + N
theorem partial_sum_le_integral (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1)) (N : ℕ) :
    ∑ i ∈ Finset.range N, f (1 + (i + 1 : ℕ)) ≤ ∫ x in (1 : ℝ)..1 + N, f x :=
  (hf.mono Set.Icc_subset_Ici_self).sum_le_integral

-- the inequalities of the book, when the series converges
theorem integral_test_bounds (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (h0 : ∀ x ∈ Set.Ici (1 : ℝ), 0 ≤ f x) (hs : Summable (fun n : ℕ => f (n + 1))) :
    ∫ x in Set.Ioi (1 : ℝ), f x ≤ ∑' n : ℕ, f (n + 1) ∧
      ∑' n : ℕ, f (n + 1) ≤ f 1 + ∫ x in Set.Ioi (1 : ℝ), f x := by
  have hi : IntegrableOn f (Set.Ioi 1) := (integral_test f hf h0).mp hs
  -- the ∫ from 1 to 1 + N tends to the ∫ from 1 to +∞
  have hI : Tendsto (fun N : ℕ => ∫ x in (1 : ℝ)..1 + N, f x) atTop
      (𝓝 (∫ x in Set.Ioi (1 : ℝ), f x)) :=
    intervalIntegral_tendsto_integral_Ioi 1 hi
      (tendsto_atTop_add_const_left atTop 1 tendsto_natCast_atTop_atTop)
  -- the partial sums f(1) + … + f(N) tend to the sum of the series
  have hS : Tendsto (fun N => ∑ i ∈ Finset.range N, f (1 + i)) atTop
      (𝓝 (∑' n : ℕ, f (n + 1))) := by
    have h := hs.hasSum.tendsto_sum_nat
    simp only [add_comm (1 : ℝ)]
    exact h
  have hS1 : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (N + 1), f (1 + i)) atTop
      (𝓝 (∑' n : ℕ, f (n + 1))) :=
    hS.comp (tendsto_add_atTop_nat 1)
  -- f(1) + f(2) + … + f(N + 1) ≤ f(1) + ∫ from 1 to 1 + N
  have h2 : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1), f (1 + i) ≤ f 1 + ∫ x in (1 : ℝ)..1 + N, f x := by
    intro N
    rw [Finset.sum_range_succ', Nat.cast_zero, add_zero]
    linarith [partial_sum_le_integral f hf N]
  exact ⟨le_of_tendsto_of_tendsto' hI hS (integral_le_partial_sum f hf),
    le_of_tendsto_of_tendsto' hS1 (hI.const_add (f 1)) h2⟩

end Ch19.KritirioOloklirwmatos
