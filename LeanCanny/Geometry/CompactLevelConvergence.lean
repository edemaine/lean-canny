/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CompactApproximation
import Mathlib.Tactic.Push

/-! # Uniform compact convergence of small levels and approximate maxima

Small nonnegative levels in a compact set approach its zero locus uniformly.
If an objective has a unique maximum on that zero locus, points with small
energy and almost maximal objective value approach the maximizer uniformly.
-/

@[expose] public section

namespace LeanCanny.Geometry.CompactLevelConvergence
open Filter Set
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

theorem small_level_in_open (K : Set X) (hK : IsCompact K) (g : X → ℝ) (hg : Continuous g)
    (hnonneg : ∀ x ∈ K, 0 ≤ g x) (U : Set X) (hU : IsOpen U)
    (hzeros : ∀ x ∈ K, g x = 0 → x ∈ U) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K, g x ≤ a → x ∈ U := by
  classical
  by_contra hn
  push Not at hn
  have ha : ∀ a : ℝ, 0 < a → ∃ x ∈ K \ U, ∀ _ : Unit, -a ≤ -g x := by
    intro a hp
    obtain ⟨x, hx, hga, hxu⟩ := hn a hp
    exact ⟨x, ⟨hx, hxu⟩, fun _ => by linarith⟩
  obtain ⟨x, hx, hneg⟩ := CompactApproximation.exists_feasible (K \ U) (hK.diff hU)
    (fun _ : Unit => fun x => -g x) (fun _ => hg.neg) ha
  have hz : g x = 0 := by linarith [hneg (), hnonneg x hx.1]
  exact hx.2 (hzeros x hx.1 hz)

theorem approximate_maximum_in_open (K : Set X) (hK : IsCompact K) (g φ : X → ℝ)
    (hg : Continuous g) (hφ : Continuous φ) (p : X)
    (hnonneg : ∀ x ∈ K, 0 ≤ g x)
    (hunique : ∀ x ∈ K, g x = 0 → φ p ≤ φ x → x = p)
    (U : Set X) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ K, g x ≤ a → φ p - a ≤ φ x → x ∈ U := by
  classical
  by_contra hn
  push Not at hn
  let f : Bool → X → ℝ := fun b x => if b then φ x - φ p else -g x
  have hf : ∀ b, Continuous (f b) := by
    intro b
    cases b
    · exact hg.neg
    · exact hφ.sub continuous_const
  have ha : ∀ a : ℝ, 0 < a → ∃ x ∈ K \ U, ∀ b, -a ≤ f b x := by
    intro a hp
    obtain ⟨x, hx, hga, hφa, hxu⟩ := hn a hp
    refine ⟨x, ⟨hx, hxu⟩, ?_⟩
    intro b
    cases b
    · change -a ≤ -g x
      linarith
    · change -a ≤ φ x - φ p
      linarith
  obtain ⟨x, hx, hfx⟩ := CompactApproximation.exists_feasible (K \ U) (hK.diff hU) f hf ha
  have hneg : 0 ≤ -g x := hfx false
  have hobj : 0 ≤ φ x - φ p := hfx true
  have hz : g x = 0 := by linarith [hnonneg x hx.1]
  have hxp := hunique x hx.1 hz (sub_nonneg.mp hobj)
  exact hx.2 (hxp.symm ▸ hpU)

theorem tendsto_of_energy_and_value {A : Type*} {l : Filter A}
    (K : Set X) (hK : IsCompact K) (g φ : X → ℝ) (hg : Continuous g) (hφ : Continuous φ) (p : X)
    (hnonneg : ∀ x ∈ K, 0 ≤ g x)
    (hunique : ∀ x ∈ K, g x = 0 → φ p ≤ φ x → x = p)
    (x : A → X) (hx : ∀ᶠ a in l, x a ∈ K)
    (henergy : Tendsto (fun a => g (x a)) l (nhds 0))
    (hvalue : Tendsto (fun a => φ (x a)) l (nhds (φ p))) : Tendsto x l (nhds p) := by
  apply tendsto_def.mpr
  intro U hU
  obtain ⟨V, hVU, hV, hpV⟩ := mem_nhds_iff.mp hU
  obtain ⟨a, ha, hm⟩ := approximate_maximum_in_open K hK g φ hg hφ p hnonneg hunique V hV hpV
  have he : ∀ᶠ i in l, g (x i) < a := henergy.eventually (Iio_mem_nhds ha)
  have hv : ∀ᶠ i in l, φ p - a < φ (x i) := hvalue.eventually (Ioi_mem_nhds (by linarith))
  filter_upwards [hx, he, hv] with i hi he hv
  exact hVU (hm (x i) hi he.le hv.le)

end LeanCanny.Geometry.CompactLevelConvergence
