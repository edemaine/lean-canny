/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryCandidateLabelLock
/-! # Literal sign-refinement membership locks the candidate over that point

The lift projects to this very original tuple. Finite gate saturation and the
positive circular retraction are exactly those of the existing refinement.
This theorem concerns membership and never replaces relative-frontier edges.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryPieceLabelLock
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def projection (d :Description) (l :CanonicalSignRefinement.Label d)
    (z :FormulaSignSlotCircularBoundedCover.Source (CanonicalSignRefinement.source d l)):
    Fin d.dimension→ℝ:=CanonicalSignRefinement.tuple d l
  (FormulaSignSlotMarginProjection.projection (CanonicalSignRefinement.source d l)
    (CanonicalAuxiliaryCandidateLabelLock.positiveProjection (CanonicalSignRefinement.source d l) z).val).val

/-- The actual closed-circular candidate component has a lift over this tuple. -/
noncomputable def Lift (d :Description) (i :CanonicalAuxiliaryCandidateCover.Index d)
    (x :Fin d.dimension→ℝ):Prop:=
  ∃hi :CanonicalAuxiliaryCandidateLabelLock.Good (CanonicalSignRefinement.source d i.1) i.2,
    ∃z :FormulaSignSlotCircularBoundedCover.Source (CanonicalSignRefinement.source d i.1),
      projection d i.1 z=x ∧JoinedIn univ
        (CanonicalAuxiliaryCandidateLabelLock.closedSample (CanonicalSignRefinement.source d i.1) i.2 hi) z

attribute [local irreducible] CanonicalSignRefinement.tuple CanonicalSignRefinement.source
  CanonicalAuxiliaryCandidateCover.sourceHomeomorph
  CanonicalAuxiliaryCandidateLabelLock.positiveProjection CanonicalAuxiliaryCandidateLabelLock.closedSample

theorem rawPiece_mem_iff (d :Description) (i :CanonicalAuxiliaryCandidateCover.Index d)
    (x :Fin d.dimension→ℝ):
    x∈(CanonicalAuxiliaryCandidateCover.data d).rawPiece i ↔Lift d i x:=by
  constructor
  · rintro ⟨old,⟨y,⟨p,Hp,Hpy⟩,Hy⟩,Hx⟩
    obtain ⟨hi,z,HZ,HJ⟩:=(CanonicalAuxiliaryCandidateLabelLock.refinement_positive_mem_iff d i.1 i.2 p).mp Hp
    refine ⟨hi,z,?_,HJ⟩
    unfold projection
    rw [HZ,Hpy]
    exact (congrArg (CanonicalSignRefinement.tuple d i.1) Hy).trans Hx
  · rintro ⟨hi,z,HZ,HJ⟩
    let p:=CanonicalAuxiliaryCandidateLabelLock.positiveProjection (CanonicalSignRefinement.source d i.1) z
    have HP:p∈((CanonicalAuxiliaryCandidateCover.data d).positiveCover i.1).piece i.2:=
      (CanonicalAuxiliaryCandidateLabelLock.refinement_positive_mem_iff d i.1 i.2 p).mpr ⟨hi,z,rfl,HJ⟩
    exact ⟨_,⟨p.val,⟨p,HP,rfl⟩,rfl⟩,HZ⟩

theorem refinement_piece_mem_iff (d :Description) (i :CanonicalAuxiliaryCandidateCover.Index d)
    (x :d.realization):
    x∈(CanonicalAuxiliaryCandidateCover.data d).piece i ↔Lift d i x.val:=
  rawPiece_mem_iff d i x.val

theorem candidate_piece_mem_iff (d :Description) (i :CanonicalAuxiliaryCandidateCover.Index d)
    (x :d.realization):x∈CanonicalAuxiliaryCandidateCover.piece d i ↔Lift d i x.val:=
  refinement_piece_mem_iff d i x

/-- The component is the literal auxiliary sample's component under the
actual integer-equation source homeomorphism. Empty candidate labels persist. -/
theorem lift_iff_component (d :Description) (i :CanonicalAuxiliaryCandidateCover.Index d)
    (x :Fin d.dimension→ℝ):Lift d i x ↔
    ∃hi :CanonicalAuxiliaryCandidateLabelLock.Good (CanonicalSignRefinement.source d i.1) i.2,
      ∃z :FormulaSignSlotCircularBoundedCover.Source (CanonicalSignRefinement.source d i.1),
        projection d i.1 z=x ∧
        CanonicalAuxiliaryCandidateCover.sourceHomeomorph (CanonicalSignRefinement.source d i.1) z∈
          connectedComponent (AuxiliaryCandidateComponentCover.sample CanonicalAuxiliaryCandidateCover.dimension_unary
            CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope
            (CanonicalSignRefinement.source d i.1) ⟨i.2,hi⟩):=by
  constructor
  · rintro ⟨hi,z,HZ,HJ⟩
    have HC:=(CanonicalAuxiliaryCandidateLabelLock.closed_mem_iff _ i.2 z).mpr ⟨hi,HJ⟩
    change CanonicalAuxiliaryCandidateCover.sourceHomeomorph (CanonicalSignRefinement.source d i.1) z∈
      SampledBitComponentCover.piece (AuxiliaryCandidateComponentCover.samples
        CanonicalAuxiliaryCandidateCover.dimension_unary CanonicalAuxiliaryCandidateCover.equation_FP
        CanonicalAuxiliaryCandidateCover.equation_scope (CanonicalSignRefinement.source d i.1)) i.2 at HC
    rw [SampledBitComponentCover.piece_of_good _ i.2 hi] at HC
    exact ⟨hi,z,HZ,HC⟩
  · rintro ⟨hi,z,HZ,HC⟩
    have HM:z∈(CanonicalAuxiliaryCandidateCover.closedCover (CanonicalSignRefinement.source d i.1)).piece i.2:=by
      change CanonicalAuxiliaryCandidateCover.sourceHomeomorph (CanonicalSignRefinement.source d i.1) z∈
        SampledBitComponentCover.piece (AuxiliaryCandidateComponentCover.samples
          CanonicalAuxiliaryCandidateCover.dimension_unary CanonicalAuxiliaryCandidateCover.equation_FP
          CanonicalAuxiliaryCandidateCover.equation_scope (CanonicalSignRefinement.source d i.1)) i.2
      rw [SampledBitComponentCover.piece_of_good _ i.2 hi]
      exact HC
    obtain ⟨hi',HJ⟩:=(CanonicalAuxiliaryCandidateLabelLock.closed_mem_iff _ i.2 z).mp HM
    exact ⟨hi',z,HZ,HJ⟩

theorem lift_sign_slot (d :Description) (i :CanonicalAuxiliaryCandidateCover.Index d)
    (x :Fin d.dimension→ℝ) (HX :Lift d i x):
    (FormulaSignSlotSource.stratum (CanonicalSignRefinement.source d i.1)).Holds
      (Formula.extend ((CanonicalSignRefinement.tuple d i.1).symm x)):=by
  have HM:=(rawPiece_mem_iff d i x).mpr HX
  obtain ⟨y,HY,HE⟩:=HM
  have HS:=FormulaSignSlotRadialAccess.projectedPiece_selected (CanonicalSignRefinement.source d i.1) _ HY
  rw [←HE,Homeomorph.symm_apply_apply]
  exact HS

theorem piece_sign_slot (d :Description) (i :CanonicalAuxiliaryCandidateCover.Index d)
    (x :d.realization) (HX :x∈CanonicalAuxiliaryCandidateCover.piece d i):
    (FormulaSignSlotSource.stratum (CanonicalSignRefinement.source d i.1)).Holds
      (Formula.extend ((CanonicalSignRefinement.tuple d i.1).symm x.val)):=
  lift_sign_slot d i x.val ((candidate_piece_mem_iff d i x).mp HX)

end LeanCanny.Connectivity.CanonicalAuxiliaryPieceLabelLock
