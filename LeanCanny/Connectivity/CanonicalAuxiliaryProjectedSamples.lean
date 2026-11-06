/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryRadialFrontier
public import LeanCanny.Connectivity.CanonicalAuxiliaryCandidateSample
/-! # Exact singleton/equality and radial alternatives for the original cover -/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryProjectedSamples
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Good (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d) : Prop :=
  CanonicalAuxiliaryCandidateLabelLock.Good (CanonicalSignRefinement.source d i.1) i.2
noncomputable def sample (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d)
    (h : Good d i) : Fin d.dimension → ℝ := CanonicalAuxiliaryCandidateCover.rawSample d i h

theorem sample_mem (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d) (h : Good d i) :
    sample d i h ∈ (CanonicalAuxiliaryCandidateCover.data d).rawPiece i :=
  CanonicalAuxiliaryCandidateCover.rawSample_mem d i h

theorem good_of_raw_nonempty (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d)
    (h : ((CanonicalAuxiliaryCandidateCover.data d).rawPiece i).Nonempty) : Good d i := by
  obtain ⟨x,a,ha,_⟩ := h
  obtain ⟨s,⟨p,hp,_⟩,_⟩ := ha
  exact (CanonicalAuxiliaryCandidateLabelLock.positive_mem_iff _ i.2 p).mp hp |>.1

theorem projected_image (c : List Bool) (i : Vertex (CanonicalAuxiliaryCandidateCover.width c)) :
    FormulaSignSlotRadialAccess.projectedPiece c ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i) =
      (fun z : FormulaSignSlotCircularBoundedCover.Source c =>
        (FormulaSignSlotCircularBoundedCover.projectedPoint c z).val) ''
          (CanonicalAuxiliaryCandidateCover.closedCover c).piece i := by
  rw [FormulaSignSlotRadialAccess.projectedPiece, FormulaSignSlotComponentMaxima.ambient,
    CanonicalAuxiliaryCandidateLabelLock.positive_piece_eq, Set.image_image, Set.image_image]
  rfl

theorem incident_iff (d : Description) (hd : d.WellFormed)
    (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    CanonicalAuxiliaryCandidateCover.edge d i j ↔
      ∃ hi : Good d i, ∃ hj : Good d j,
        sample d i hi = sample d j hj ∨
        (∃ x ∈ (CanonicalAuxiliaryCandidateCover.data d).rawPiece i,
          CanonicalAuxiliaryRadialFrontier.descriptorAt d j x) ∨
        (∃ x ∈ (CanonicalAuxiliaryCandidateCover.data d).rawPiece j,
          CanonicalAuxiliaryRadialFrontier.descriptorAt d i x) := by
  constructor
  · intro H
    have HR := (CanonicalAuxiliaryRadialFrontier.incident_iff_raw d hd i j).mp H
    rcases (CanonicalAuxiliaryRadialFrontier.raw_incident_iff d i j).mp HR with ⟨x,hi,hj⟩ | HI | HJ
    · have hgi := good_of_raw_nonempty d i (by rw [hi]; exact ⟨x,mem_singleton x⟩)
      have hgj := good_of_raw_nonempty d j (by rw [hj]; exact ⟨x,mem_singleton x⟩)
      have HSi := sample_mem d i hgi
      have HSj := sample_mem d j hgj
      rw [hi] at HSi
      rw [hj] at HSj
      exact ⟨hgi,hgj,Or.inl ((show sample d i hgi = x from HSi).trans (show sample d j hgj = x from HSj).symm)⟩
    · obtain ⟨x,hx,hD⟩ := HI
      have hgi := good_of_raw_nonempty d i ⟨x,hx⟩
      have hgj : Good d j := hD.elim (fun D => D.good)
      exact ⟨hgi,hgj,Or.inr (Or.inl ⟨x,hx,hD⟩)⟩
    · obtain ⟨x,hx,hD⟩ := HJ
      have hgj := good_of_raw_nonempty d j ⟨x,hx⟩
      have hgi : Good d i := hD.elim (fun D => D.good)
      exact ⟨hgi,hgj,Or.inr (Or.inr ⟨x,hx,hD⟩)⟩
  · rintro ⟨hi,hj,H⟩
    apply (CanonicalAuxiliaryRadialFrontier.incident_iff_raw d hd i j).mpr
    rcases H with HE | HI | HJ
    · left
      refine ⟨sample d i hi,sample_mem d i hi,?_⟩
      rw [HE]
      exact subset_closure (sample_mem d j hj)
    · obtain ⟨x,hx,hD⟩ := HI
      exact Or.inl ⟨x,hx,(CanonicalAuxiliaryRadialFrontier.raw_closure_iff d j x).mpr (Or.inr hD)⟩
    · obtain ⟨x,hx,hD⟩ := HJ
      exact Or.inr ⟨x,hx,(CanonicalAuxiliaryRadialFrontier.raw_closure_iff d i x).mpr (Or.inr hD)⟩

end LeanCanny.Connectivity.CanonicalAuxiliaryProjectedSamples
