/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryPieceLabelLock
public import LeanCanny.Connectivity.CanonicalAuxiliaryBitFrontier
/-! # The actual bounded frontier piece retains its decoded sign and component

Invalid raw labels denote the empty literal piece. Valid labels retain the
exact sign-slot source, auxiliary candidate, and a closed lift over the given
original point. The frontier edge definition is unchanged.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryBitPieceLabelLock
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def DecodedLift (d :Description) (w :List Bool) (x :Fin d.dimension→ℝ):Prop:=
  ∃hv :CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) w),
    CanonicalAuxiliaryPieceLabelLock.Lift d (CanonicalAuxiliaryCandidateLabels.decode d w hv) x

section Decoding
attribute [local irreducible] CanonicalAuxiliaryCandidateCover.dimension CanonicalAuxiliaryCandidateCover.equation
  CanonicalAuxiliaryCandidateCover.width CanonicalAuxiliaryCandidateCover.labelBudget
  CanonicalAuxiliaryCandidateLabels.sign CanonicalAuxiliaryCandidateLabels.source
  CanonicalAuxiliaryCandidateLabels.candidate CanonicalAuxiliaryCandidateLabels.padding
  pair ClosedFormulaGateMetadata.count

theorem decoded_sign (d :Description) (w :List Bool)
    (hv :CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) w)):
    (CanonicalAuxiliaryCandidateLabels.decode d w hv).1.val=
      CanonicalAuxiliaryCandidateLabels.sign (pair (CanonicalSignRefinement.original d) w):=rfl
theorem decoded_source (d :Description) (w :List Bool)
    (hv :CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) w)):
    CanonicalSignRefinement.source d (CanonicalAuxiliaryCandidateLabels.decode d w hv).1=
      CanonicalAuxiliaryCandidateLabels.source (pair (CanonicalSignRefinement.original d) w):=
  CanonicalAuxiliaryCandidateLabels.source_accepted d w hv
theorem decoded_candidate (d :Description) (w :List Bool)
    (hv :CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) w)):
    (CanonicalAuxiliaryCandidateLabels.decode d w hv).2.val=
      CanonicalAuxiliaryCandidateLabels.candidate (pair (CanonicalSignRefinement.original d) w):=rfl
end Decoding

theorem piece_mem_iff_of_valid (d :Description) (i :Vertex (CanonicalAuxiliaryBitFrontier.width d))
    (hv :CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) i.val))
    (x :d.realization):x∈CanonicalAuxiliaryBitFrontier.piece d i ↔
      CanonicalAuxiliaryPieceLabelLock.Lift d (CanonicalAuxiliaryCandidateLabels.decode d i.val hv) x.val:=by
  simpa only [CanonicalAuxiliaryBitFrontier.piece,dite_eq_left hv] using
    CanonicalAuxiliaryPieceLabelLock.candidate_piece_mem_iff d (CanonicalAuxiliaryCandidateLabels.decode d i.val hv) x

theorem piece_eq_empty_of_invalid (d :Description) (i :Vertex (CanonicalAuxiliaryBitFrontier.width d))
    (hv :¬CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) i.val)):
    CanonicalAuxiliaryBitFrontier.piece d i=∅:=by
  exact dite_eq_right hv

theorem piece_mem_iff (d :Description) (i :Vertex (CanonicalAuxiliaryBitFrontier.width d))
    (x :d.realization):x∈CanonicalAuxiliaryBitFrontier.piece d i ↔DecodedLift d i.val x.val:=by
  by_cases hv :CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) i.val)
  · rw [piece_mem_iff_of_valid d i hv x]
    exact ⟨fun H=>⟨hv,H⟩,fun ⟨_,H⟩=>H⟩
  · rw [piece_eq_empty_of_invalid d i hv]
    constructor
    · exact fun H=>False.elim H
    · rintro ⟨HV,_⟩
      exact False.elim (hv HV)

/-- This names the actual integer source component, not a substitute graph. -/
noncomputable def DecodedComponentLift (d :Description) (w :List Bool) (x :Fin d.dimension→ℝ):Prop:=
  ∃hv :CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) w),
    ∃hi :CanonicalAuxiliaryCandidateLabelLock.Good
      (CanonicalSignRefinement.source d (CanonicalAuxiliaryCandidateLabels.decode d w hv).1)
      (CanonicalAuxiliaryCandidateLabels.decode d w hv).2,
      ∃z :FormulaSignSlotCircularBoundedCover.Source
        (CanonicalSignRefinement.source d (CanonicalAuxiliaryCandidateLabels.decode d w hv).1),
        CanonicalAuxiliaryPieceLabelLock.projection d (CanonicalAuxiliaryCandidateLabels.decode d w hv).1 z=x ∧
        CanonicalAuxiliaryCandidateCover.sourceHomeomorph
          (CanonicalSignRefinement.source d (CanonicalAuxiliaryCandidateLabels.decode d w hv).1) z∈
          connectedComponent (AuxiliaryCandidateComponentCover.sample CanonicalAuxiliaryCandidateCover.dimension_unary
            CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope
            (CanonicalSignRefinement.source d (CanonicalAuxiliaryCandidateLabels.decode d w hv).1)
            ⟨(CanonicalAuxiliaryCandidateLabels.decode d w hv).2,hi⟩)

theorem piece_mem_iff_component (d :Description) (i :Vertex (CanonicalAuxiliaryBitFrontier.width d))
    (x :d.realization):x∈CanonicalAuxiliaryBitFrontier.piece d i ↔DecodedComponentLift d i.val x.val:=by
  rw [piece_mem_iff]
  constructor
  · rintro ⟨hv,H⟩
    exact ⟨hv,(CanonicalAuxiliaryPieceLabelLock.lift_iff_component d _ x.val).mp H⟩
  · rintro ⟨hv,H⟩
    exact ⟨hv,(CanonicalAuxiliaryPieceLabelLock.lift_iff_component d _ x.val).mpr H⟩

theorem piece_sign_slot (d :Description) (i :Vertex (CanonicalAuxiliaryBitFrontier.width d))
    (x :d.realization) (HX :x∈CanonicalAuxiliaryBitFrontier.piece d i):
    ∃hv :CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) i.val),
      (FormulaSignSlotSource.stratum
        (CanonicalSignRefinement.source d (CanonicalAuxiliaryCandidateLabels.decode d i.val hv).1)).Holds
        (Formula.extend ((CanonicalSignRefinement.tuple d (CanonicalAuxiliaryCandidateLabels.decode d i.val hv).1).symm x.val)):=by
  obtain ⟨hv,H⟩:=(piece_mem_iff d i x).mp HX
  exact ⟨hv,CanonicalAuxiliaryPieceLabelLock.lift_sign_slot d _ x.val H⟩

end LeanCanny.Connectivity.CanonicalAuxiliaryBitPieceLabelLock
