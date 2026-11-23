-- Companion digital material for the book: Matzakos, N. (2026).
-- Elements of Linear Algebra, Differential & Integral Calculus. Independently published.
-- Chapter 19 · Properties of Limits of Sequences · checked with Lean v4.37.0-rc1 and Mathlib (23/11/2026).

import Mathlib

namespace Ch19.IdiotitesOriwn
open Filter Topology

-- limit of a sum, with ε-N
theorem sum_rule (a b : ℕ → ℝ) (A B : ℝ) (ha : Tendsto a atTop (𝓝 A))
    (hb : Tendsto b atTop (𝓝 B)) : Tendsto (fun n => a n + b n) atTop (𝓝 (A + B)) := by
  rw [Metric.tendsto_atTop] at ha hb ⊢
  intro ε hε
  -- N₁ for ε/2 in a and N₂ for ε/2 in b
  obtain ⟨N₁, hN₁⟩ := ha (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hb (ε / 2) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_of_max_le_left hn)
  have h2 := hN₂ n (le_of_max_le_right hn)
  rw [Real.dist_eq] at h1 h2 ⊢
  -- triangle inequality
  calc |a n + b n - (A + B)| = |(a n - A) + (b n - B)| := by congr 1; ring
    _ ≤ |a n - A| + |b n - B| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

theorem diff_rule (a b : ℕ → ℝ) (A B : ℝ) (ha : Tendsto a atTop (𝓝 A))
    (hb : Tendsto b atTop (𝓝 B)) : Tendsto (fun n => a n - b n) atTop (𝓝 (A - B)) := by
  have h := sum_rule a (fun n => -b n) A (-B) ha hb.neg
  simp only [← sub_eq_add_neg] at h
  exact h

theorem mul_rule (a b : ℕ → ℝ) (A B : ℝ) (ha : Tendsto a atTop (𝓝 A))
    (hb : Tendsto b atTop (𝓝 B)) : Tendsto (fun n => a n * b n) atTop (𝓝 (A * B)) :=
  ha.mul hb

theorem div_rule (a b : ℕ → ℝ) (A B : ℝ) (ha : Tendsto a atTop (𝓝 A))
    (hb : Tendsto b atTop (𝓝 B)) (hB : B ≠ 0) :
    Tendsto (fun n => a n / b n) atTop (𝓝 (A / B)) :=
  ha.div hb hB

theorem abs_rule (a : ℕ → ℝ) (A : ℝ) (ha : Tendsto a atTop (𝓝 A)) :
    Tendsto (fun n => |a n|) atTop (𝓝 |A|) :=
  ha.abs

theorem npow_rule (a : ℕ → ℝ) (A : ℝ) (k : ℕ) (ha : Tendsto a atTop (𝓝 A)) :
    Tendsto (fun n => a n ^ k) atTop (𝓝 (A ^ k)) :=
  ha.pow k

theorem zpow_rule (a : ℕ → ℝ) (A : ℝ) (k : ℤ) (ha : Tendsto a atTop (𝓝 A)) (hA : A ≠ 0) :
    Tendsto (fun n => a n ^ k) atTop (𝓝 (A ^ k)) :=
  ha.zpow₀ k (Or.inl hA)

theorem pow_rule (a : ℕ → ℝ) (A p : ℝ) (ha : Tendsto a atTop (𝓝 A)) (hA : 0 < A) :
    Tendsto (fun n => a n ^ p) atTop (𝓝 (A ^ p)) :=
  ha.rpow_const (Or.inl hA.ne')

theorem squeeze (a b c : ℕ → ℝ) (L : ℝ) (ha : Tendsto a atTop (𝓝 L))
    (hb : Tendsto b atTop (𝓝 L)) (hac : ∀ n, a n ≤ c n) (hcb : ∀ n, c n ≤ b n) :
    Tendsto c atTop (𝓝 L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le ha hb hac hcb

end Ch19.IdiotitesOriwn
