/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FrontierCover

/-! # Clopen path covers obtained from finite recursive decompositions

Saturating the labels of a finite accessible cover by graph reachability
gives clopen path-connected pieces. Labels and empty pieces are retained.
Membership is an existential finite-label search followed by a graph test.
-/

@[expose] public section

namespace LeanCanny.Connectivity
open Set

structure ClopenPathCover (X I : Type*) [TopologicalSpace X] where
  piece : I → Set X
  clopen : ∀ i, IsClopen (piece i)
  cover : ∀ x, ∃ i, x ∈ piece i
  paths : ∀ i, ∀ x ∈ piece i, ∀ y ∈ piece i, JoinedIn (piece i) x y

namespace ClopenPathCover
variable {X I : Type*} [TopologicalSpace X]

/-- Transfer a recursive cover along an explicit homeomorphism, retaining
the same labels and membership queries. -/
def comap {Y : Type*} [TopologicalSpace Y] (C : ClopenPathCover Y I)
    (e : X ≃ₜ Y) : ClopenPathCover X I where
  piece := fun i => e ⁻¹' C.piece i
  clopen := fun i => (C.clopen i).preimage e.continuous
  cover := fun x => C.cover (e x)
  paths := by
    intro i x hx y hy
    have hj := (C.paths i (e x) hx (e y) hy).map e.symm.continuous.continuousOn
    have hsub : e.symm '' C.piece i ⊆ e ⁻¹' C.piece i := by
      rintro z ⟨w, hw, rfl⟩
      simpa only [mem_preimage, Homeomorph.apply_symm_apply] using hw
    simpa only [Homeomorph.symm_apply_apply] using hj.mono hsub

/-- Recursive accessible slice covers supply the clopen pieces required for
attaching adjacent slabs. No connected-component oracle is an input. -/
def ofAccessible [Finite I] (piece : I → Set X) (cover : ∀ x, ∃ i, x ∈ piece i)
    (access : ∀ i, FrontierCover.Accessible (piece i)) : ClopenPathCover X I where
  piece := FrontierCover.component piece
  clopen := FrontierCover.component_isClopen piece cover
  cover := FrontierCover.component_cover piece cover
  paths := FrontierCover.component_paths piece cover access

/-- A recursively constructed closed path cover can be saturated for use as
an endpoint component cover at the next level. -/
def ofClosed [Finite I] (piece : I → Set X) (closed : ∀ i, IsClosed (piece i))
    (cover : ∀ x, ∃ i, x ∈ piece i)
    (paths : ∀ i, ∀ x ∈ piece i, ∀ y ∈ piece i, JoinedIn (piece i) x y) : ClopenPathCover X I :=
  ofAccessible piece cover (fun i x hx y hy => by
    have hx' : x ∈ piece i := (closed i).closure_eq ▸ hx
    simpa only [insert_eq_of_mem hx'] using paths i x hx' y hy)

theorem mem_ofAccessible_iff [Finite I] (piece : I → Set X) (cover : ∀ x, ∃ i, x ∈ piece i)
    (access : ∀ i, FrontierCover.Accessible (piece i)) (i : I) (x : X) :
    x ∈ (ofAccessible piece cover access).piece i ↔
      ∃ j, Relation.ReflTransGen (FrontierCover.Incident piece) i j ∧ x ∈ piece j := Iff.rfl

section Ambient
variable {S : Set X} (C : ClopenPathCover S I)

def imagePiece (i : I) : Set X := Subtype.val '' C.piece i

theorem imagePiece_subset (i : I) : C.imagePiece i ⊆ S := by
  rintro x ⟨z, _, rfl⟩
  exact z.property

theorem imagePiece_closed (hS : IsClosed S) (i : I) : IsClosed (C.imagePiece i) :=
  hS.isClosedEmbedding_subtypeVal.isClosedMap _ (C.clopen i).isClosed

theorem imagePiece_paths (i : I) (x : X) (hx : x ∈ C.imagePiece i)
    (y : X) (hy : y ∈ C.imagePiece i) : JoinedIn (C.imagePiece i) x y := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact (C.paths i u hu v hv).map continuous_subtype_val.continuousOn

theorem imagePiece_cover (x : X) (hx : x ∈ S) : ∃ i, x ∈ C.imagePiece i := by
  obtain ⟨i, hi⟩ := C.cover ⟨x, hx⟩
  exact ⟨i, ⟨x, hx⟩, hi, rfl⟩

/-- A connected limit in the slice stays in any clopen slice piece containing
one of its points. In particular, it stays with its critical-branch endpoint. -/
theorem subset_imagePiece_of_isPreconnected {L : Set X} (hL : IsPreconnected L)
    (hsub : L ⊆ S) {i : I} {z : X} (hz : z ∈ L) (hzi : z ∈ C.imagePiece i) :
    L ⊆ C.imagePiece i := by
  have himage : Subtype.val '' ((Subtype.val : S → X) ⁻¹' L) = L := by
    apply image_preimage_eq_of_subset
    intro x hx
    exact ⟨⟨x, hsub hx⟩, rfl⟩
  have hc : IsPreconnected ((Subtype.val : S → X) ⁻¹' L) := by
    apply Topology.IsEmbedding.subtypeVal.isInducing.isPreconnected_image.mp
    rwa [himage]
  obtain ⟨w, hw, rfl⟩ := hzi
  have hkeep := hc.subset_isClopen (C.clopen i) ⟨w, hz, hw⟩
  intro x hx
  exact ⟨⟨x, hsub hx⟩, hkeep hx, rfl⟩

end Ambient

end ClopenPathCover
end LeanCanny.Connectivity
