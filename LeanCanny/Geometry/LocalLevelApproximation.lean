/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith

/-! # Nearby positive levels from a continuous positive path

A path starting at a zero and having positive energy for positive times meets
every sufficiently small positive level inside any prescribed neighborhood.
-/

@[expose] public section

namespace LeanCanny.Geometry.LocalLevelApproximation
open Set Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

def Recovery (g : X → ℝ) (p : X) : Prop :=
  ∀ U : Set X, U ∈ nhds p → ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
    ∃ x ∈ U, g x = alpha

theorem of_positive_path (g : X → ℝ) (hg : Continuous g) (γ : ℝ → X) (hγ : Continuous γ)
    (hzero : g (γ 0) = 0) (hpos : ∀ t : ℝ, 0 < t → 0 < g (γ t)) : Recovery g (γ 0) := by
  intro U hU
  have hpre : γ ⁻¹' U ∈ nhds (0 : ℝ) := hγ.continuousAt.preimage_mem_nhds hU
  obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.mp hpre
  let b := e / 2
  have hb : 0 < b := by dsimp [b]; linarith
  refine ⟨g (γ b), hpos b hb, ?_⟩
  intro alpha hp hs
  have hm : alpha ∈ Set.Icc (g (γ 0)) (g (γ b)) := by rw [hzero]; exact ⟨hp.le, hs.le⟩
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hb.le (hg.comp hγ).continuousOn hm
  refine ⟨γ t, ?_, hgt⟩
  apply hball
  change dist t 0 < e
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  exact ht.2.trans_lt (by dsimp [b]; linarith)

theorem high_value (g φ : X → ℝ) (p : X) (hrec : Recovery g p) (hφ : Continuous φ)
    (K : Set X) (hpK : p ∈ interior K) (b : ℝ) (hb : 0 < b) :
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∃ x ∈ K, g x = alpha ∧ φ p - b < φ x := by
  let U := interior K ∩ {x | φ p - b < φ x}
  have hU : U ∈ nhds p := inter_mem (isOpen_interior.mem_nhds hpK)
    (hφ.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith)))
  obtain ⟨a, ha, hr⟩ := hrec U hU
  exact ⟨a, ha, fun alpha hp hs => by
    obtain ⟨x, hx, hgx⟩ := hr alpha hp hs
    exact ⟨x, interior_subset hx.1, hgx, hx.2⟩⟩

end LeanCanny.Geometry.LocalLevelApproximation
