/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Finite sample bounds for connected components

A fixed finite family meeting every component bounds the number of components.
Unused samples outside the set are allowed; they map to a fallback point.
-/

@[expose] public section
namespace LeanCanny.Geometry.ComponentFiniteSamples
open Set
open scoped Classical
variable {X I : Type*} [TopologicalSpace X]

noncomputable def componentMap (S : Set X) (point : I → X) (fallback : S) : I → ConnectedComponents S :=
  fun i => ConnectedComponents.mk (if hi : point i ∈ S then ⟨point i, hi⟩ else fallback)

lemma componentMap_spec (S : Set X) (point : I → X) (fallback : S) (i : I) (hi : point i ∈ S) :
    componentMap S point fallback i = ConnectedComponents.mk ⟨point i, hi⟩ := by
  simp only [componentMap, dite_eq_left hi]

theorem componentMap_surjective (S : Set X) (point : I → X) (fallback : S)
    (hcover : ∀ x ∈ S, ∃ i, point i ∈ connectedComponentIn S x) :
    Function.Surjective (componentMap S point fallback) := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨i, hi⟩ := hcover x.val x.property
  have hp : point i ∈ S := connectedComponentIn_subset S x.val hi
  have H : point i ∈ Subtype.val '' connectedComponent x := by
    simpa only [connectedComponentIn_eq_image x.property] using hi
  obtain ⟨y, hy, he⟩ := H
  have HY : (⟨point i, hp⟩ : S) = y := Subtype.ext he.symm
  refine ⟨i, ?_⟩
  rw [componentMap_spec S point fallback i hp, HY]
  exact ConnectedComponents.coe_eq_coe'.mpr hy

theorem finite_card_le [Finite I] (S : Set X) (point : I → X)
    (hcover : ∀ x ∈ S, ∃ i, point i ∈ connectedComponentIn S x) :
    Finite (ConnectedComponents S) ∧ Nat.card (ConnectedComponents S) ≤ Nat.card I := by
  by_cases hs : S.Nonempty
  · let fallback : S := ⟨Classical.choose hs, Classical.choose_spec hs⟩
    have H := componentMap_surjective S point fallback hcover
    exact ⟨Finite.of_surjective _ H, Nat.card_le_card_of_surjective _ H⟩
  · let : IsEmpty S := ⟨fun x => hs ⟨x.val, x.property⟩⟩
    let : IsEmpty (ConnectedComponents S) := Function.Surjective.isEmpty ConnectedComponents.surjective_coe
    exact ⟨inferInstance, by simp⟩

end LeanCanny.Geometry.ComponentFiniteSamples
