/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotCandidateRadialDescriptor
public import LeanCanny.Connectivity.CanonicalAuxiliaryBitPieceLabelLock
/-! # Actual refinement closure has a same-label finite real radial receipt

Closure in the original realization remains relative closure. The common-point
case is kept separately, and invalid bit labels remain empty. No edge relation
or native complexity claim is substituted for the literal frontier definition.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryRadialClosure
open Set LeanCanny.Encoding LeanCanny.Geometry LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev Descriptor (d :Description) (i :CanonicalAuxiliaryCandidateCover.Index d)
    (x :Fin d.dimension→ℝ):=
  FormulaSignSlotCandidateRadialDescriptor.Descriptor (CanonicalSignRefinement.source d i.1) i.2
    ((CanonicalSignRefinement.tuple d i.1).symm x)

attribute [local irreducible] CanonicalSignRefinement.tuple CanonicalSignRefinement.source
  CanonicalAuxiliaryCandidateCover.width

theorem rawPiece_closure_iff (d :Description) (i :CanonicalAuxiliaryCandidateCover.Index d)
    (x :Fin d.dimension→ℝ):
    x∈closure ((CanonicalAuxiliaryCandidateCover.data d).rawPiece i) ↔
      x∈(CanonicalAuxiliaryCandidateCover.data d).rawPiece i ∨Nonempty (Descriptor d i x):=by
  let P:=FormulaSignSlotRadialAccess.projectedPiece (CanonicalSignRefinement.source d i.1)
    ((CanonicalAuxiliaryCandidateLabelLock.positiveCover (CanonicalSignRefinement.source d i.1)).piece i.2)
  have HE:x∈closure ((CanonicalAuxiliaryCandidateCover.data d).rawPiece i) ↔
      (CanonicalSignRefinement.tuple d i.1).symm x∈closure P:=by
    change x∈closure (CanonicalSignRefinement.tuple d i.1 '' P) ↔_
    rw [(CanonicalSignRefinement.tuple d i.1).isClosedMap.closure_image_eq_of_continuous
      (CanonicalSignRefinement.tuple d i.1).continuous]
    constructor
    · rintro ⟨y,HY,HP⟩
      have HI:=(congrArg (CanonicalSignRefinement.tuple d i.1).symm HP)
      rw [Homeomorph.symm_apply_apply] at HI
      exact HI ▸ HY
    · intro HY
      exact ⟨_,HY,(CanonicalSignRefinement.tuple d i.1).apply_symm_apply x⟩
  have HM:x∈(CanonicalAuxiliaryCandidateCover.data d).rawPiece i ↔
      (CanonicalSignRefinement.tuple d i.1).symm x∈P:=by
    constructor
    · rintro ⟨y,HY,HP⟩
      have HI:=congrArg (CanonicalSignRefinement.tuple d i.1).symm HP
      rw [Homeomorph.symm_apply_apply] at HI
      exact HI ▸ HY
    · intro HY
      exact ⟨_,HY,(CanonicalSignRefinement.tuple d i.1).apply_symm_apply x⟩
  rw [HE,FormulaSignSlotCandidateRadialDescriptor.projected_closure_iff,←HM]

theorem piece_closure_iff (d :Description) (hd :d.WellFormed)
    (i :CanonicalAuxiliaryCandidateCover.Index d) (x :d.realization):
    x∈closure (CanonicalAuxiliaryCandidateCover.piece d i) ↔
      x∈CanonicalAuxiliaryCandidateCover.piece d i ∨Nonempty (Descriptor d i x.val):=by
  have HImage:(Subtype.val :d.realization→Fin d.dimension→ℝ) '' CanonicalAuxiliaryCandidateCover.piece d i=
      (CanonicalAuxiliaryCandidateCover.data d).rawPiece i:=by
    change (Subtype.val :d.realization→Fin d.dimension→ℝ) ''
      (Subtype.val ⁻¹' (CanonicalAuxiliaryCandidateCover.data d).rawPiece i)=_
    apply image_preimage_eq_of_subset
    intro point HP
    exact ⟨⟨point,CanonicalSignRefinement.ClosedCovers.rawPiece_subset hd
      (CanonicalAuxiliaryCandidateCover.data d) i HP⟩,rfl⟩
  have HC:x∈closure (CanonicalAuxiliaryCandidateCover.piece d i) ↔
      x.val∈closure ((CanonicalAuxiliaryCandidateCover.data d).rawPiece i):=by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    change x.val∈closure ((Subtype.val :d.realization→Fin d.dimension→ℝ) ''
      CanonicalAuxiliaryCandidateCover.piece d i) ↔_
    rw [HImage]
  rw [HC,rawPiece_closure_iff]
  rfl

theorem bit_piece_closure_iff (d :Description) (hd :d.WellFormed)
    (i :Vertex (CanonicalAuxiliaryBitFrontier.width d)) (x :d.realization):
    x∈closure (CanonicalAuxiliaryBitFrontier.piece d i) ↔
      x∈CanonicalAuxiliaryBitFrontier.piece d i ∨
      ∃hv :CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) i.val),
        Nonempty (Descriptor d (CanonicalAuxiliaryCandidateLabels.decode d i.val hv) x.val):=by
  by_cases hv:CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) i.val)
  · have HE:CanonicalAuxiliaryBitFrontier.piece d i=
        CanonicalAuxiliaryCandidateCover.piece d (CanonicalAuxiliaryCandidateLabels.decode d i.val hv):=by
      exact dite_eq_left hv
    rw [HE,piece_closure_iff d hd]
    constructor
    · rintro (HM|HD)
      · exact Or.inl HM
      · exact Or.inr ⟨hv,HD⟩
    · rintro (HM|⟨_,HD⟩)
      · exact Or.inl HM
      · exact Or.inr HD
  · rw [CanonicalAuxiliaryBitPieceLabelLock.piece_eq_empty_of_invalid d i hv,closure_empty]
    constructor
    · exact fun H=>False.elim H
    · rintro (H|⟨HV,_⟩)
      · exact False.elim H
      · exact False.elim (hv HV)

end LeanCanny.Connectivity.CanonicalAuxiliaryRadialClosure
