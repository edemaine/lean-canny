/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialDescriptorSingleton
public import LeanCanny.Connectivity.CanonicalAuxiliaryBitFrontier
/-! # Actual Boolean-cover frontiers reduce to singleton or radial cases -/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryRadialFrontier
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem closure_image_iff {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (P : Set X) (D : X → Prop)
    (H : ∀ a, a ∈ closure P ↔ P = {a} ∨ D a) (y : Y) :
    y ∈ closure (e '' P) ↔ e '' P = {y} ∨ D (e.symm y) := by
  have HS : e '' P = {y} ↔ P = {e.symm y} := by
    rw [←show e '' {e.symm y} = {y} by simp only [Set.image_singleton,e.apply_symm_apply],
      e.injective.image_injective.eq_iff]
  rw [←e.image_closure,e.image_eq_preimage_symm,mem_preimage,H,HS]

noncomputable def descriptorAt (d : Description) (t : CanonicalAuxiliaryCandidateCover.Index d)
    (x : Fin d.dimension → ℝ) : Prop :=
  Nonempty (FormulaSignSlotCandidateRadialDescriptor.Descriptor (CanonicalSignRefinement.source d t.1)
    t.2 ((CanonicalSignRefinement.tuple d t.1).symm x))

theorem raw_closure_iff (d : Description) (t : CanonicalAuxiliaryCandidateCover.Index d)
    (x : Fin d.dimension → ℝ) :
    x ∈ closure ((CanonicalAuxiliaryCandidateCover.data d).rawPiece t) ↔
      (CanonicalAuxiliaryCandidateCover.data d).rawPiece t = {x} ∨ descriptorAt d t x :=
  closure_image_iff (CanonicalSignRefinement.tuple d t.1)
    (FormulaSignSlotRadialAccess.projectedPiece (CanonicalSignRefinement.source d t.1)
      ((CanonicalAuxiliaryCandidateLabelLock.positiveCover (CanonicalSignRefinement.source d t.1)).piece t.2))
    (fun a => Nonempty (FormulaSignSlotCandidateRadialDescriptor.Descriptor
      (CanonicalSignRefinement.source d t.1) t.2 a))
    (fun a => FormulaSignSlotRadialDescriptorSingleton.closure_iff _ _ a) x

private theorem incident_alternative {X I : Type*} [TopologicalSpace X]
    (P : I → Set X) (D : I → X → Prop)
    (H : ∀ i x, x ∈ closure (P i) ↔ P i = {x} ∨ D i x) (i j : I) :
    FrontierCover.Incident P i j ↔
      (∃ x, P i = {x} ∧ P j = {x}) ∨
      (∃ x ∈ P i, D j x) ∨ (∃ x ∈ P j, D i x) := by
  have step (a b : I) (x : X) (ha : x ∈ P a) (hb : x ∈ closure (P b)) :
      (∃ x, P a = {x} ∧ P b = {x}) ∨
      (∃ x ∈ P a, D b x) ∨ (∃ x ∈ P b, D a x) := by
    have hA := (H a x).mp (subset_closure ha)
    have hB := (H b x).mp hb
    clear H
    aesop
  constructor
  · rintro (⟨x,ha,hb⟩ | ⟨x,hb,ha⟩)
    · exact step i j x ha hb
    · simpa only [and_comm,or_comm,or_left_comm,or_assoc] using step j i x hb ha
  · rintro (⟨x,hi,hj⟩ | ⟨x,hi,hDj⟩ | ⟨x,hj,hDi⟩)
    · exact Or.inl ⟨x,hi ▸ mem_singleton x,subset_closure (hj ▸ mem_singleton x)⟩
    · exact Or.inl ⟨x,hi,(H j x).mpr (Or.inr hDj)⟩
    · exact Or.inr ⟨x,hj,(H i x).mpr (Or.inr hDi)⟩

theorem raw_incident_iff (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    FrontierCover.Incident (CanonicalAuxiliaryCandidateCover.data d).rawPiece i j ↔
      (∃ x, (CanonicalAuxiliaryCandidateCover.data d).rawPiece i = {x} ∧
        (CanonicalAuxiliaryCandidateCover.data d).rawPiece j = {x}) ∨
      (∃ x ∈ (CanonicalAuxiliaryCandidateCover.data d).rawPiece i, descriptorAt d j x) ∨
      (∃ x ∈ (CanonicalAuxiliaryCandidateCover.data d).rawPiece j, descriptorAt d i x) :=
  incident_alternative _ (descriptorAt d) (raw_closure_iff d) i j

theorem piece_closure_eq (d : Description) (hd : d.WellFormed)
    (i : CanonicalAuxiliaryCandidateCover.Index d) :
    closure (CanonicalAuxiliaryCandidateCover.piece d i) =
      Subtype.val ⁻¹' closure ((CanonicalAuxiliaryCandidateCover.data d).rawPiece i) := by
  change closure (Subtype.val ⁻¹' (CanonicalAuxiliaryCandidateCover.data d).rawPiece i : Set d.realization) = _
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    Subtype.image_preimage_val,inter_eq_right.mpr
      (CanonicalSignRefinement.ClosedCovers.rawPiece_subset hd (CanonicalAuxiliaryCandidateCover.data d) i)]

theorem incident_iff_raw (d : Description) (hd : d.WellFormed)
    (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    FrontierCover.Incident (CanonicalAuxiliaryCandidateCover.piece d) i j ↔
      FrontierCover.Incident (CanonicalAuxiliaryCandidateCover.data d).rawPiece i j :=
  FrontierCover.incident_preimage_iff _ Topology.IsEmbedding.subtypeVal
    (fun t => by
      simpa using CanonicalSignRefinement.ClosedCovers.rawPiece_subset hd
        (CanonicalAuxiliaryCandidateCover.data d) t) i j

end LeanCanny.Connectivity.CanonicalAuxiliaryRadialFrontier
