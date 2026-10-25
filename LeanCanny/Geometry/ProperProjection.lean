/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Maps.Proper.Basic

/-! # Proper projection of a closed family with compactly bounded unknowns

The parameter space need not be compact. A closed family in `A × E` projects
properly to `A` if all its unknown coordinates lie in a fixed compact set.
This supplies properness for bounded root families without assuming a global
enumeration of their branches.
-/

@[expose] public section

namespace LeanCanny.Geometry.ProperProjection
open Set Topology

theorem isProperMap_fst {A E : Type*} [TopologicalSpace A] [TopologicalSpace E]
    {S : Set (A × E)} (hS : IsClosed S) {K : Set E} (hK : IsCompact K)
    (hbound : ∀ z ∈ S, z.2 ∈ K) :
    IsProperMap (fun z : S => z.val.1) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let r : S → A × K := fun z => (z.val.1, ⟨z.val.2, hbound z.val z.property⟩)
  let j : A × K → A × E := fun z => (z.1, z.2.val)
  have hr : Continuous r :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  have hj : Continuous j := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hcomp : IsEmbedding (j ∘ r) := IsEmbedding.subtypeVal
  have hemb : IsEmbedding r := IsEmbedding.of_comp hr hj hcomp
  have hrange : range r = j ⁻¹' S := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact w.property
    · intro hz
      refine ⟨⟨j z, hz⟩, ?_⟩
      apply Prod.ext
      · rfl
      · exact Subtype.ext rfl
  have hclosed : IsClosed (range r) := hrange ▸ hS.preimage hj
  have hrproper : IsProperMap r := (show IsClosedEmbedding r from ⟨hemb, hclosed⟩).isProperMap
  exact (isProperMap_fst_of_compactSpace : IsProperMap (Prod.fst : A × K → A)).comp hrproper

/-- A closed family lying on the level graph of a proper function projects
properly. Unlike a fixed compact bound, this permits its unknown coordinates
to grow when the parameter goes to infinity. -/
theorem isProperMap_fst_of_level {A E : Type*} [TopologicalSpace A] [TopologicalSpace E]
    {S : Set (A × E)} (hS : IsClosed S) {g : E → A} (hg : IsProperMap g)
    (hlevel : ∀ z ∈ S, z.1 = g z.2) :
    IsProperMap (fun z : S => z.val.1) := by
  let r : S → E := fun z => z.val.2
  let j : E → A × E := fun x => (g x, x)
  have hr : Continuous r := continuous_snd.comp continuous_subtype_val
  have hj : Continuous j := hg.continuous.prodMk continuous_id
  have hcomp : j ∘ r = (Subtype.val : S → A × E) := by
    funext z
    exact Prod.ext (hlevel z.val z.property).symm rfl
  have hemb : IsEmbedding r := IsEmbedding.of_comp hr hj (by rw [hcomp]; exact IsEmbedding.subtypeVal)
  have hrange : range r = j ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      change (g z.val.2, z.val.2) ∈ S
      have hz : (g z.val.2, z.val.2) = z.val := Prod.ext (hlevel z.val z.property).symm rfl
      rw [hz]
      exact z.property
    · intro hx
      exact ⟨⟨j x, hx⟩, rfl⟩
  have hrproper : IsProperMap r :=
    (show IsClosedEmbedding r from ⟨hemb, hrange ▸ hS.preimage hj⟩).isProperMap
  have heq : g ∘ r = (fun z : S => z.val.1) := by
    funext z
    exact (hlevel z.val z.property).symm
  simpa only [heq] using hg.comp hrproper

end LeanCanny.Geometry.ProperProjection
