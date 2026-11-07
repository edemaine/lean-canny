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
  change x∈closure (CanonicalSignRefinement.tuple d i.1 '' P) ↔
    x∈CanonicalSignRefinement.tuple d i.1 '' P ∨_
  rw [←(CanonicalSignRefinement.tuple d i.1).image_closure,
    (CanonicalSignRefinement.tuple d i.1).image_eq_preimage_symm,
    (CanonicalSignRefinement.tuple d i.1).image_eq_preimage_symm]
  exact FormulaSignSlotCandidateRadialDescriptor.projected_closure_iff _ _ _

theorem piece_closure_iff (d :Description) (hd :d.WellFormed)
    (i :CanonicalAuxiliaryCandidateCover.Index d) (x :d.realization):
    x∈closure (CanonicalAuxiliaryCandidateCover.piece d i) ↔
      x∈CanonicalAuxiliaryCandidateCover.piece d i ∨Nonempty (Descriptor d i x.val):=by
  change x∈closure (Subtype.val ⁻¹' (CanonicalAuxiliaryCandidateCover.data d).rawPiece i :
    Set d.realization) ↔_
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    Subtype.image_preimage_val,inter_eq_right.mpr
      (CanonicalSignRefinement.ClosedCovers.rawPiece_subset hd (CanonicalAuxiliaryCandidateCover.data d) i)]
  exact rawPiece_closure_iff d i x.val

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
    simp only [hv, exists_true_left]
  · simp [CanonicalAuxiliaryBitPieceLabelLock.piece_eq_empty_of_invalid d i hv,hv]

end LeanCanny.Connectivity.CanonicalAuxiliaryRadialClosure
