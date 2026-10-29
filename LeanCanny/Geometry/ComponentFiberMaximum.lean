/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RegularFiber
public import Mathlib.Topology.Order.Compact

/-! # A local maximum in each component of a compact regular fiber -/

@[expose] public section
namespace LeanCanny.Geometry.ComponentFiberMaximum
open Set Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_joined_localMax (f : E → F) (c : F) (φ : E → ℝ)
    (hf : ∀ x : RegularFiber.Fiber f c, ContDiffAt ℝ 1 f x.val)
    (hD : ∀ x : RegularFiber.Fiber f c, Function.Surjective (fderiv ℝ f x.val))
    (hcompact : IsCompact {x : E | f x = c}) (hφ : Continuous φ)
    (x : E) (hx : f x = c) :
    ∃ y : E, f y = c ∧ JoinedIn {z | f z = c} x y ∧ IsLocalMaxOn φ {z | f z = c} y := by
  let L := RegularFiber.Fiber f c
  let : LocallyPathConnectedSpace L := RegularFiber.locallyPathConnected f c hf hD
  let : CompactSpace L := isCompact_iff_compactSpace.mp hcompact
  let x' : L := ⟨x, hx⟩
  have hC : IsCompact (connectedComponent x') := isClosed_connectedComponent.isCompact
  have hobj : Continuous (fun z : L => φ z.val) := hφ.comp continuous_subtype_val
  obtain ⟨y, hy, hmax⟩ := hC.exists_isMaxOn ⟨x', mem_connectedComponent⟩ hobj.continuousOn
  have hlocal : IsLocalMaxOn φ {z | f z = c} y.val := by
    change ∀ᶠ z in 𝓝[{z | f z = c}] y.val, φ z ≤ φ y.val
    rw [← map_nhds_subtype_val (s := {z | f z = c}) y]
    exact hmax.isLocalMax (isOpen_connectedComponent.mem_nhds hy)
  have hj : Joined x' y := by
    apply mem_pathComponent_iff.mp
    rwa [pathComponent_eq_connectedComponent]
  have hj' := (joinedIn_univ.mpr hj).map continuous_subtype_val.continuousOn
  refine ⟨y.val, y.property, hj'.mono ?_, hlocal⟩
  rintro z ⟨w, _, rfl⟩
  exact w.property

end LeanCanny.Geometry.ComponentFiberMaximum
