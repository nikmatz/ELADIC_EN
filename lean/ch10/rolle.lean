-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 10 · Rolle's Theorem · checked with Lean v4.37.0-rc1 and Mathlib (22/11/2026).

import Mathlib

namespace Ch10.Rolle
open Filter Topology

theorem endpoint_value (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hfab : f a = f b) (x : ℝ)
    (hx : x ∈ Set.Icc a b) (hxi : x ∉ Set.Ioo a b) : f x = f a := by
  have h : x ∈ ({a, b} : Set ℝ) := by
    rw [← Set.Icc_sdiff_Ioo_same hab]
    exact ⟨hx, hxi⟩
  rcases h with h | h
  · rw [h]
  · rw [Set.mem_singleton_iff] at h
    rw [h, hfab]

theorem rolle (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hfc : ContinuousOn f (Set.Icc a b))
    (hfab : f a = f b) (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) :
    ∃ c ∈ Set.Ioo a b, f' c = 0 := by
  obtain ⟨M, hM, hMax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hab.le) hfc
  obtain ⟨m, hm, hMin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hab.le) hfc
  by_cases hMi : M ∈ Set.Ioo a b
  · have hloc : IsLocalMax f M := hMax.isLocalMax (Icc_mem_nhds hMi.1 hMi.2)
    exact ⟨M, hMi, hloc.hasDerivAt_eq_zero (hff' M hMi)⟩
  by_cases hmi : m ∈ Set.Ioo a b
  · have hloc : IsLocalMin f m := hMin.isLocalMin (Icc_mem_nhds hmi.1 hmi.2)
    exact ⟨m, hmi, hloc.hasDerivAt_eq_zero (hff' m hmi)⟩
  have hfM : f M = f a := endpoint_value f a b hab.le hfab M hM hMi
  have hfm : f m = f a := endpoint_value f a b hab.le hfab m hm hmi
  have hconst : ∀ x ∈ Set.Ioo a b, f x = f a := by
    intro x hx
    have h1 : f x ≤ f M := isMaxOn_iff.mp hMax x (Set.Ioo_subset_Icc_self hx)
    have h2 : f m ≤ f x := isMinOn_iff.mp hMin x (Set.Ioo_subset_Icc_self hx)
    linarith
  have hc : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have hd : HasDerivAt f 0 ((a + b) / 2) := by
    apply (hasDerivAt_const ((a + b) / 2) (f a)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hc.1 hc.2] with x hx
    exact hconst x hx
  exact ⟨(a + b) / 2, hc, (hff' _ hc).unique hd⟩

theorem between_roots (f f' : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hfc : ContinuousOn f (Set.Icc a b))
    (hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) (ha : f a = 0) (hb : f b = 0) :
    ∃ c ∈ Set.Ioo a b, f' c = 0 :=
  rolle f f' a b hab hfc (by rw [ha, hb]) hff'

end Ch10.Rolle
