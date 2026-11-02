/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FiniteComponentCover
public import Mathlib.Topology.Connected.LocallyConnected
/-! # Finite components in a neighborhood basis imply local connectedness -/
@[expose] public section
namespace LeanCanny.Geometry.FiniteComponentNeighborhoods
open Set Filter
open scoped Classical Topology
variable {X : Type*} [TopologicalSpace X]

theorem locallyConnected (h : ∀ x : X, ∀ U∈𝓝 x, ∃ K : Set X,
    K∈𝓝 x ∧ K⊆U ∧ Finite (ConnectedComponents K)) : LocallyConnectedSpace X := by
  apply locallyConnectedSpace_iff_connected_subsets.mpr
  intro x U HU
  obtain ⟨K,HK,HKU,HF⟩ := h x U HU
  let : Finite (ConnectedComponents K) := HF
  let z : K := ⟨x,mem_of_mem_nhds HK⟩
  let C := connectedComponent z
  have HC : IsOpen C := (FiniteComponentCover.isClopen_component z).isOpen
  have HN : Subtype.val '' C∈𝓝[K] x := by
    rw [← map_nhds_subtype_val z,Filter.image_mem_map_iff Subtype.val_injective]
    exact HC.mem_nhds mem_connectedComponent
  rw [nhdsWithin_eq_nhds.mpr HK] at HN
  refine ⟨Subtype.val '' C,HN,isPreconnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn,?_⟩
  rintro y ⟨v,_HV,rfl⟩
  exact HKU v.property
end LeanCanny.Geometry.FiniteComponentNeighborhoods
