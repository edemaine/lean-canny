/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryJointHeader
public import LeanCanny.Connectivity.CanonicalAuxiliaryProjectedSamples
public import LeanCanny.Connectivity.FormulaSignSlotRadialSourceCasts
public import LeanCanny.Connectivity.FormulaSignSlotRadialJointFeasibility
/-! # Original radial frontier data have the literal guarded joint header -/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryRadialCodec
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private def reindex (u : List Bool) (i j : Vertex (CanonicalAuxiliaryCandidateCover.width u))
    (a b : Fin (FormulaSignSlotSource.dimension u) → ℝ) (hi : i = j) (ha : a = b)
    (D : FormulaSignSlotCandidateRadialDescriptor.Descriptor u i a) :
    FormulaSignSlotCandidateRadialDescriptor.Descriptor u j b := by
  cases hi
  cases ha
  exact D

private theorem closed_atLabel (side : Bool) (c : List Bool)
    (y : FormulaSignSlotRadialJointStratumLabels.Space c)
    (hg : FormulaSignSlotRadialJointStratumLabels.Good side c)
    (hp : JoinedIn Set.univ (FormulaSignSlotRadialJointStratumLabels.sample side c hg)
      (FormulaSignSlotRadialJointStratumLabels.project side c y)) :
    FormulaSignSlotRadialJointStratumLabels.project side c y ∈
      (CanonicalAuxiliaryCandidateCover.closedCover (FormulaSignSlotRadialJointStratumLabels.source side c)).piece
        (FormulaSignSlotRadialJointClosureGeometry.labelVertex side c hg) := by
  apply (CanonicalAuxiliaryCandidateLabelLock.closed_mem_iff _ _ _).mpr
  exact ⟨FormulaSignSlotRadialJointClosureGeometry.labelVertex_good side c hg,
    by rwa [FormulaSignSlotRadialJointClosureGeometry.closedSample_eq]⟩

theorem header_center (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d)
    (A : FormulaSignSlotCircularBoundedCover.Source (CanonicalSignRefinement.source d i.1)) :
    FormulaSignSlotRadialSourceCasts.vector (CanonicalAuxiliaryJointHeader.source_true d i j).symm
      ((CanonicalSignRefinement.tuple d j.1).symm (CanonicalSignRefinement.tuple d i.1
        (FormulaSignSlotCircularBoundedCover.projectedPoint (CanonicalSignRefinement.source d i.1) A).val)) =
      FormulaSignSlotRadialJointRealization.leftCenter (CanonicalAuxiliaryJointHeader.header d i j)
        (FormulaSignSlotRadialSourceCasts.source (CanonicalAuxiliaryJointHeader.source_false d i j).symm A) := by
  apply FormulaSignSlotRadialSourceCasts.equal_of_extend
  exact (FormulaSignSlotRadialSourceCasts.vector_extend _ _).trans
    ((FormulaSignSlotRadialSourceCasts.tuple_symm_extend d j.1 _).trans
      ((CanonicalSignRefinement.extend_tuple d i.1 _).trans
        ((FormulaSignSlotRadialSourceCasts.projected_extend
          (CanonicalAuxiliaryJointHeader.source_false d i j).symm A).symm.trans
            (FormulaSignSlotRadialSourceCasts.leftCenter_extend _ _).symm)))

theorem feasible_of_raw_descriptor (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d)
    (h : ∃ x ∈ (CanonicalAuxiliaryCandidateCover.data d).rawPiece i,
      CanonicalAuxiliaryRadialFrontier.descriptorAt d j x) :
    FormulaSignSlotRadialJointFeasibility.Feasible (CanonicalAuxiliaryJointHeader.header d i j) := by
  obtain ⟨x,⟨a,ha,hax⟩,HD⟩ := h
  have HAP : a ∈ FormulaSignSlotRadialAccess.projectedPiece (CanonicalSignRefinement.source d i.1)
      ((CanonicalAuxiliaryCandidateLabelLock.positiveCover (CanonicalSignRefinement.source d i.1)).piece i.2) := ha
  rw [CanonicalAuxiliaryProjectedSamples.projected_image] at HAP
  obtain ⟨A,hA,hAa⟩ := HAP
  have HX : CanonicalSignRefinement.tuple d i.1
      (FormulaSignSlotCircularBoundedCover.projectedPoint (CanonicalSignRefinement.source d i.1) A).val = x :=
    (congrArg (CanonicalSignRefinement.tuple d i.1) hAa).trans hax
  obtain ⟨D⟩ := HD
  have DX : FormulaSignSlotCandidateRadialDescriptor.Descriptor (CanonicalSignRefinement.source d j.1) j.2
      ((CanonicalSignRefinement.tuple d j.1).symm (CanonicalSignRefinement.tuple d i.1
        (FormulaSignSlotCircularBoundedCover.projectedPoint (CanonicalSignRefinement.source d i.1) A).val)) := HX.symm ▸ D
  let H := CanonicalAuxiliaryJointHeader.header d i j
  let AL := FormulaSignSlotRadialSourceCasts.source (CanonicalAuxiliaryJointHeader.source_false d i j).symm A
  let IL := FormulaSignSlotRadialSourceCasts.vertex (CanonicalAuxiliaryJointHeader.source_false d i j).symm i.2
  let JR := FormulaSignSlotRadialSourceCasts.vertex (CanonicalAuxiliaryJointHeader.source_true d i j).symm j.2
  let D0 := FormulaSignSlotRadialSourceCasts.descriptor (CanonicalAuxiliaryJointHeader.source_true d i j).symm
    j.2 _ DX
  let D1 := reindex _ JR JR _ _ rfl (header_center d i j A) D0
  have HL : IL.val = CanonicalAuxiliaryCandidateLabels.candidate (FormulaSignSlotRadialJointLayout.labelQuery false H) :=
    (FormulaSignSlotRadialSourceCasts.vertex_val _ i.2).trans (CanonicalAuxiliaryJointHeader.candidate_false d i j).symm
  have HR : JR.val = CanonicalAuxiliaryCandidateLabels.candidate (FormulaSignSlotRadialJointLayout.labelQuery true H) :=
    (FormulaSignSlotRadialSourceCasts.vertex_val _ j.2).trans (CanonicalAuxiliaryJointHeader.candidate_true d i j).symm
  have HM := FormulaSignSlotRadialSourceCasts.closed_mem (CanonicalAuxiliaryJointHeader.source_false d i j).symm A i.2 hA
  obtain ⟨k,_,y,HB,HG,HC⟩ := FormulaSignSlotRadialJointDescriptorLift.exists_labelled_lift H AL JR D1 IL HL HR HM
  exact ⟨k,y,HB,HG,HC⟩

theorem raw_descriptor_of_feasible (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d)
    (h : FormulaSignSlotRadialJointFeasibility.Feasible (CanonicalAuxiliaryJointHeader.header d i j)) :
    ∃ x ∈ (CanonicalAuxiliaryCandidateCover.data d).rawPiece i,
      CanonicalAuxiliaryRadialFrontier.descriptorAt d j x := by
  obtain ⟨k,y,HB,HG,HC⟩ := h
  let H := CanonicalAuxiliaryJointHeader.header d i j
  let c := FormulaSignSlotRadialJointStratum.packet H k
  have HH : FormulaSignSlotRadialJointStratum.header c = H := LeanCanny.pairFst_pair _ _
  have HL : FormulaSignSlotRadialJointStratumLabels.source false c = CanonicalSignRefinement.source d i.1 :=
    (congrArg (FormulaSignSlotRadialJointLayout.source false) HH).trans (CanonicalAuxiliaryJointHeader.source_false d i j)
  have HR : FormulaSignSlotRadialJointStratumLabels.source true c = CanonicalSignRefinement.source d j.1 :=
    (congrArg (FormulaSignSlotRadialJointLayout.source true) HH).trans (CanonicalAuxiliaryJointHeader.source_true d i j)
  obtain ⟨hgL,hpL⟩ := HB false
  obtain ⟨hgR,hpR⟩ := HB true
  let iC := FormulaSignSlotRadialJointClosureGeometry.labelVertex false c hgL
  let jC := FormulaSignSlotRadialJointClosureGeometry.labelVertex true c hgR
  let A := FormulaSignSlotRadialJointStratumLabels.project false c y
  let AO := FormulaSignSlotRadialSourceCasts.source HL A
  have HLV : iC.val = i.2.val :=
    (congrArg (fun u => CanonicalAuxiliaryCandidateLabels.candidate
      (FormulaSignSlotRadialJointLayout.labelQuery false u)) HH).trans
        (CanonicalAuxiliaryJointHeader.candidate_false d i j)
  have HRV : jC.val = j.2.val :=
    (congrArg (fun u => CanonicalAuxiliaryCandidateLabels.candidate
      (FormulaSignSlotRadialJointLayout.labelQuery true u)) HH).trans
        (CanonicalAuxiliaryJointHeader.candidate_true d i j)
  have HLI : FormulaSignSlotRadialSourceCasts.vertex HL iC = i.2 :=
    Subtype.ext ((FormulaSignSlotRadialSourceCasts.vertex_val HL iC).trans HLV)
  have HRJ : FormulaSignSlotRadialSourceCasts.vertex HR jC = j.2 :=
    Subtype.ext ((FormulaSignSlotRadialSourceCasts.vertex_val HR jC).trans HRV)
  have HAM : A ∈ (CanonicalAuxiliaryCandidateCover.closedCover
      (FormulaSignSlotRadialJointStratumLabels.source false c)).piece iC :=
    closed_atLabel false c y hgL hpL
  have HAOM : AO ∈ (CanonicalAuxiliaryCandidateCover.closedCover (CanonicalSignRefinement.source d i.1)).piece i.2 :=
    HLI ▸ FormulaSignSlotRadialSourceCasts.closed_mem HL A iC HAM
  let x := CanonicalSignRefinement.tuple d i.1
    (FormulaSignSlotCircularBoundedCover.projectedPoint (CanonicalSignRefinement.source d i.1) AO).val
  have HE : Formula.extend (FormulaSignSlotRadialJointDescriptorGeometry.center c y) =
      Formula.extend (FormulaSignSlotCircularBoundedCover.projectedPoint
        (FormulaSignSlotRadialJointStratumLabels.source false c) A).val :=
    (congrArg Formula.extend (FormulaSignSlotRadialJointDescriptorGeometry.center_left_projection c y)).trans
      (FormulaSignSlotRadialSourceCasts.leftCenter_extend _ A)
  have HX : FormulaSignSlotRadialSourceCasts.vector HR
      (FormulaSignSlotRadialJointDescriptorGeometry.center c y) = (CanonicalSignRefinement.tuple d j.1).symm x := by
    apply FormulaSignSlotRadialSourceCasts.equal_of_extend
    exact (FormulaSignSlotRadialSourceCasts.vector_extend HR _).trans
      (HE.trans ((FormulaSignSlotRadialSourceCasts.projected_extend HL A).symm.trans
        ((CanonicalSignRefinement.extend_tuple d i.1 _).symm.trans
          (FormulaSignSlotRadialSourceCasts.tuple_symm_extend d j.1 x).symm)))
  let DC := FormulaSignSlotRadialJointDescriptorGeometry.descriptor c y jC
    (FormulaSignSlotRadialJointClosureGeometry.labelVertex_good true c hgR)
    (by rwa [FormulaSignSlotRadialJointClosureGeometry.closedSample_eq]) HG HC
  let DO := FormulaSignSlotRadialSourceCasts.descriptor HR jC _ DC
  refine ⟨x,?_,⟨reindex _ _ _ _ _ HRJ HX DO⟩⟩
  refine ⟨_,?_,rfl⟩
  have HP : (FormulaSignSlotCircularBoundedCover.projectedPoint (CanonicalSignRefinement.source d i.1) AO).val ∈
      FormulaSignSlotRadialAccess.projectedPiece (CanonicalSignRefinement.source d i.1)
        ((CanonicalAuxiliaryCandidateLabelLock.positiveCover (CanonicalSignRefinement.source d i.1)).piece i.2) := by
    rw [CanonicalAuxiliaryProjectedSamples.projected_image]
    exact ⟨AO,HAOM,rfl⟩
  exact HP

theorem feasible_iff_raw_descriptor (d : Description) (i j : CanonicalAuxiliaryCandidateCover.Index d) :
    FormulaSignSlotRadialJointFeasibility.Feasible (CanonicalAuxiliaryJointHeader.header d i j) ↔
      ∃ x ∈ (CanonicalAuxiliaryCandidateCover.data d).rawPiece i,
        CanonicalAuxiliaryRadialFrontier.descriptorAt d j x :=
  ⟨raw_descriptor_of_feasible d i j, feasible_of_raw_descriptor d i j⟩

end LeanCanny.Connectivity.CanonicalAuxiliaryRadialCodec
