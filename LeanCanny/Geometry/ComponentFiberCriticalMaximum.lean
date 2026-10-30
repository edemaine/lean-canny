/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RegularFiber
public import Mathlib.Topology.Order.Compact

/-! # Component maxima in compact fibers with singularities

At a regular point an implicit-function chart places a connected neighborhood
inside its component. A maximum on a compact component is therefore either
singular or a local maximum on the entire fiber. No global regularity or
local path connectivity at singular points is assumed.
-/

@[expose] public section
namespace LeanCanny.Geometry.ComponentFiberCriticalMaximum
open Set Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem component_mem_nhds (f : E → F) (c : F) (a : RegularFiber.Fiber f c)
    (hf : ContDiffAt ℝ 1 f a.val) (hD : Function.Surjective (fderiv ℝ f a.val)) :
    connectedComponent a ∈ 𝓝 a := by
  let e := RegularFiber.chart f c a (fderiv ℝ f a.val) (hf.hasStrictFDerivAt one_ne_zero) hD
  have ha : a ∈ e.source := RegularFiber.mem_chart_source f c a _ (hf.hasStrictFDerivAt one_ne_zero) hD
  let : LocallyPathConnectedSpace e.target := e.open_target.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace e.source := e.toHomeomorphSourceTarget.symm.locallyPathConnectedSpace
  let a' : e.source := ⟨a, ha⟩
  have HA : connectedComponent a' ∈ 𝓝 a' := isOpen_connectedComponent.mem_nhds mem_connectedComponent
  have H : Subtype.val '' connectedComponent a' ∈ 𝓝 a :=
    e.open_source.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds HA
  apply Filter.mem_of_superset H
  exact continuous_subtype_val.image_connectedComponent_subset a'

theorem exists_component_critical_max (f : E → F) (c : F) (obj : E → ℝ)
    (hf : ∀ x : RegularFiber.Fiber f c, ContDiffAt ℝ 1 f x.val)
    (hcompact : IsCompact {x : E | f x = c}) (hobj : Continuous obj)
    (x : E) (hx : f x = c) :
    ∃ y : E, f y = c ∧ y ∈ connectedComponentIn {z | f z = c} x ∧
      (¬Function.Surjective (fderiv ℝ f y) ∨
        Function.Surjective (fderiv ℝ f y) ∧ IsLocalMaxOn obj {z | f z = c} y) := by
  let L := RegularFiber.Fiber f c
  let : CompactSpace L := isCompact_iff_compactSpace.mp hcompact
  let x' : L := ⟨x, hx⟩
  have hC : IsCompact (connectedComponent x') := isClosed_connectedComponent.isCompact
  have ho : Continuous (fun z : L => obj z.val) := hobj.comp continuous_subtype_val
  obtain ⟨y, hy, hm⟩ := hC.exists_isMaxOn ⟨x', mem_connectedComponent⟩ ho.continuousOn
  refine ⟨y.val, y.property, ?_, ?_⟩
  · rw [connectedComponentIn_eq_image hx]
    exact ⟨y, hy, rfl⟩
  · by_cases hr : Function.Surjective (fderiv ℝ f y.val)
    · right
      refine ⟨hr, ?_⟩
      change ∀ᶠ z in 𝓝[{z | f z = c}] y.val, obj z ≤ obj y.val
      rw [← map_nhds_subtype_val (s := {z | f z = c}) y]
      apply hm.isLocalMax
      rw [connectedComponent_eq hy]
      exact component_mem_nhds f c y (hf y) hr
    · exact Or.inl hr

end LeanCanny.Geometry.ComponentFiberCriticalMaximum
