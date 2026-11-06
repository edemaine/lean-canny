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
  constructor
  · intro hy
    rw [← e.image_closure] at hy
    obtain ⟨a,ha,hay⟩ := hy
    rcases (H a).mp ha with HS | HD
    · left
      rw [HS, Set.image_singleton, hay]
    · right
      have HE : a = e.symm y := by rw [← hay, e.symm_apply_apply]
      exact HE ▸ HD
  · rintro (HS | HD)
    · rw [HS]
      exact subset_closure (mem_singleton y)
    · rw [← e.image_closure]
      exact ⟨e.symm y,(H _).mpr (Or.inr HD),e.apply_symm_apply y⟩

private theorem subtype_closure {X : Type*} [TopologicalSpace X]
    (s P : Set X) (hP : P ⊆ s) :
    closure (Subtype.val ⁻¹' P : Set s) = Subtype.val ⁻¹' closure P := by
  have HI : Subtype.val '' (Subtype.val ⁻¹' P : Set s) = P := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,hP hx⟩,hx,rfl⟩
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, HI]

private theorem subtype_incident {X I : Type*} [TopologicalSpace X]
    (s : Set X) (P : I → Set X) (hP : ∀ i, P i ⊆ s) (i j : I) :
    FrontierCover.Incident (fun i => (Subtype.val ⁻¹' P i : Set s)) i j ↔
      FrontierCover.Incident P i j := by
  constructor
  · rintro (⟨x,hi,hj⟩ | ⟨x,hj,hi⟩)
    · left
      rw [subtype_closure s (P j) (hP j)] at hj
      exact ⟨x.val,hi,hj⟩
    · right
      rw [subtype_closure s (P i) (hP i)] at hi
      exact ⟨x.val,hj,hi⟩
  · rintro (⟨x,hi,hj⟩ | ⟨x,hj,hi⟩)
    · left
      refine ⟨⟨x,hP i hi⟩,hi,?_⟩
      rw [subtype_closure s (P j) (hP j)]
      exact hj
    · right
      refine ⟨⟨x,hP j hj⟩,hj,?_⟩
      rw [subtype_closure s (P i) (hP i)]
      exact hi

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
    rcases (H b x).mp hb with HSb | HDb
    · have hxb : x ∈ P b := by rw [HSb]; exact mem_singleton x
      rcases (H a x).mp (subset_closure ha) with HSa | HDa
      · exact Or.inl ⟨x,HSa,HSb⟩
      · exact Or.inr (Or.inr ⟨x,hxb,HDa⟩)
    · exact Or.inr (Or.inl ⟨x,ha,HDb⟩)
  constructor
  · rintro (⟨x,ha,hb⟩ | ⟨x,hb,ha⟩)
    · exact step i j x ha hb
    · rcases step j i x hb ha with ⟨y,hj,hi⟩ | HJ | HI
      · exact Or.inl ⟨y,hi,hj⟩
      · exact Or.inr (Or.inr HJ)
      · exact Or.inr (Or.inl HI)
  · rintro (⟨x,hi,hj⟩ | ⟨x,hi,hDj⟩ | ⟨x,hj,hDi⟩)
    · left
      refine ⟨x,?_,?_⟩
      · rw [hi]; exact mem_singleton x
      · rw [hj]; exact subset_closure (mem_singleton x)
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
      Subtype.val ⁻¹' closure ((CanonicalAuxiliaryCandidateCover.data d).rawPiece i) :=
  subtype_closure d.realization ((CanonicalAuxiliaryCandidateCover.data d).rawPiece i)
    (CanonicalSignRefinement.ClosedCovers.rawPiece_subset hd (CanonicalAuxiliaryCandidateCover.data d) i)

theorem incident_iff_raw (d : Description) (hd : d.WellFormed)
    (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    FrontierCover.Incident (CanonicalAuxiliaryCandidateCover.piece d) i j ↔
      FrontierCover.Incident (CanonicalAuxiliaryCandidateCover.data d).rawPiece i j :=
  subtype_incident d.realization (CanonicalAuxiliaryCandidateCover.data d).rawPiece
    (fun t => CanonicalSignRefinement.ClosedCovers.rawPiece_subset hd (CanonicalAuxiliaryCandidateCover.data d) t) i j

end LeanCanny.Connectivity.CanonicalAuxiliaryRadialFrontier
