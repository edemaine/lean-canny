/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith

/-! # Zeros detected by bounded minima of a coercive deformation -/

public section

namespace LeanCanny.CountingHierarchy

open Filter Set
open scoped Topology

variable {X : Type*} [MetricSpace X]

/-- A nonnegative perturbation of a function with compact sublevel sets
 attains its minimum, including when the perturbation parameter is zero. -/
theorem exists_minimizer_of_compact_sublevels (F G : X → ℝ)
    (hF : Continuous F) (hG : Continuous G) (hFn : ∀ x, 0 ≤ F x)
    (hcompact : ∀ B : ℝ, IsCompact {x | G x ≤ B})
    (x₀ : X) (u : ℝ) (hu : 0 ≤ u) :
    ∃ x : X, IsMinOn (fun y => G y + u * F y) univ x := by
  let B := G x₀ + u * F x₀
  have hx₀ : G x₀ ≤ B := le_add_of_nonneg_right (mul_nonneg hu (hFn x₀))
  have hc : Continuous (fun y => G y + u * F y) := hG.add (continuous_const.mul hF)
  obtain ⟨x, hx, hmin⟩ := (hcompact B).exists_isMinOn ⟨x₀, hx₀⟩ hc.continuousOn
  refine ⟨x, ?_⟩
  intro y _
  by_cases hy : G y ≤ B
  · exact hmin hy
  · have hb : G x + u * F x ≤ B := hmin hx₀
    have hnonneg := mul_nonneg hu (hFn y)
    exact hb.trans ((le_of_not_ge hy).trans (le_add_of_nonneg_right hnonneg))

/-- Uniformly bounded values along the deformation detect an actual zero
 by compactness. The reverse direction uses any zero as a comparison point. -/
theorem zero_iff_bounded_coercive_deformation (F G : X → ℝ)
    (hF : Continuous F) (hFn : ∀ x, 0 ≤ F x) (hGn : ∀ x, 0 ≤ G x)
    (hcompact : ∀ B : ℝ, IsCompact {x | G x ≤ B}) :
    (∃ x : X, F x = 0) ↔
      ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u → ∃ x : X, G x + u * F x ≤ B := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨G x, fun u _ => ⟨x, by simp [hx]⟩⟩
  · rintro ⟨B, hB⟩
    choose x hx using (fun k : ℕ => hB ((k : ℝ) + 1) (by positivity))
    have hGbound (k : ℕ) : G (x k) ≤ B :=
      (le_add_of_nonneg_right (mul_nonneg (by positivity) (hFn _))).trans (hx k)
    obtain ⟨a, _ha, σ, hσ, ht⟩ := (hcompact B).tendsto_subseq hGbound
    have hFconv : Tendsto (fun k => F (x (σ k))) atTop (𝓝 (F a)) :=
      hF.continuousAt.tendsto.comp ht
    have hupper : Tendsto (fun k => B / ((σ k : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero, Function.comp_def] using
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp hσ.tendsto_atTop).const_mul B
    have hle : F a ≤ 0 := le_of_tendsto_of_tendsto hFconv hupper (Eventually.of_forall (fun k => by
      apply (le_div_iff₀ (by positivity : 0 < (σ k : ℝ) + 1)).mpr
      have hh := hx (σ k)
      have hg := hGn (x (σ k))
      nlinarith))
    exact ⟨a, le_antisymm hle (hFn a)⟩

end LeanCanny.CountingHierarchy
