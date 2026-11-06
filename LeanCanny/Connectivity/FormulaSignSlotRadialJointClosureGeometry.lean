/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialJointDescriptorGeometry
/-! # The actual joint labels give the two original projected pieces -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialJointClosureGeometry
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def labelVertex (side : Bool) (c : List Bool)
    (h : FormulaSignSlotRadialJointStratumLabels.Good side c) :
    Vertex (CanonicalAuxiliaryCandidateCover.width (FormulaSignSlotRadialJointStratumLabels.source side c)) :=
  ⟨FormulaSignSlotRadialJointStratumLabels.label side c, by
    have H := (Classical.choose h).1.1
    simpa only [CanonicalAuxiliaryCandidateCover.width, pairFst_pair, pairSnd_pair] using H⟩

theorem labelVertex_good (side : Bool) (c : List Bool)
    (h : FormulaSignSlotRadialJointStratumLabels.Good side c) :
    CanonicalAuxiliaryCandidateLabelLock.Good (FormulaSignSlotRadialJointStratumLabels.source side c)
      (labelVertex side c h) := h

theorem closedSample_eq (side : Bool) (c : List Bool)
    (h : FormulaSignSlotRadialJointStratumLabels.Good side c) :
    CanonicalAuxiliaryCandidateLabelLock.closedSample (FormulaSignSlotRadialJointStratumLabels.source side c)
      (labelVertex side c h) (labelVertex_good side c h) =
        FormulaSignSlotRadialJointStratumLabels.sample side c h := rfl

theorem atLabel_closed_mem (side : Bool) (c : List Bool)
    (x : FormulaSignSlotRadialJointStratumLabels.Space c)
    (h : FormulaSignSlotRadialJointStratumLabels.AtLabel side c x) :
    ∃ i : Vertex (CanonicalAuxiliaryCandidateCover.width (FormulaSignSlotRadialJointStratumLabels.source side c)),
      i.val = FormulaSignSlotRadialJointStratumLabels.label side c ∧
      FormulaSignSlotRadialJointStratumLabels.project side c x ∈
        (CanonicalAuxiliaryCandidateCover.closedCover (FormulaSignSlotRadialJointStratumLabels.source side c)).piece i := by
  obtain ⟨hg,hp⟩ := h
  refine ⟨labelVertex side c hg,rfl,?_⟩
  apply (CanonicalAuxiliaryCandidateLabelLock.closed_mem_iff _ _ _).mpr
  exact ⟨labelVertex_good side c hg, by rwa [closedSample_eq]⟩

theorem atLabel_iff_closed_mem (side : Bool) (c : List Bool)
    (x : FormulaSignSlotRadialJointStratumLabels.Space c) :
    FormulaSignSlotRadialJointStratumLabels.AtLabel side c x ↔
    ∃ i : Vertex (CanonicalAuxiliaryCandidateCover.width (FormulaSignSlotRadialJointStratumLabels.source side c)),
      i.val = FormulaSignSlotRadialJointStratumLabels.label side c ∧
      FormulaSignSlotRadialJointStratumLabels.project side c x ∈
        (CanonicalAuxiliaryCandidateCover.closedCover (FormulaSignSlotRadialJointStratumLabels.source side c)).piece i := by
  constructor
  · exact atLabel_closed_mem side c x
  · rintro ⟨i,hi,hm⟩
    obtain ⟨hg,_⟩ := (CanonicalAuxiliaryCandidateLabelLock.closed_mem_iff _ _ _).mp hm
    have hgood : FormulaSignSlotRadialJointStratumLabels.Good side c := by
      change AuxiliaryCandidateComponentCover.Good CanonicalAuxiliaryCandidateCover.dimension_unary
        CanonicalAuxiliaryCandidateCover.equation_FP CanonicalAuxiliaryCandidateCover.equation_scope
        (FormulaSignSlotRadialJointStratumLabels.source side c)
        (FormulaSignSlotRadialJointStratumLabels.label side c)
      rw [← hi]
      exact hg
    have HI : i = labelVertex side c hgood := Subtype.ext hi
    rw [HI] at hm
    obtain ⟨hg',hp⟩ := (CanonicalAuxiliaryCandidateLabelLock.closed_mem_iff _ _ _).mp hm
    have HS : CanonicalAuxiliaryCandidateLabelLock.closedSample _ _ hg' =
        FormulaSignSlotRadialJointStratumLabels.sample side c hgood := rfl
    exact ⟨hgood, HS ▸ hp⟩

open FormulaSignSlotRadialJointDescriptorGeometry

theorem guarded_projected_closures (c : List Bool)
    (x : FormulaSignSlotRadialJointStratumLabels.Space c)
    (h : FormulaSignSlotRadialJointStratumLabels.BothLabels c x)
    (hg : (anchor c x).val.val ∈ FormulaSignSlotRadialParameterGrid.grid
      (FormulaSignSlotRadialJointStratumLabels.source true c) (center c x) (radius c x))
    (hc : ∀ t ∈ Ioo 0 (bound c x), t ∉ FormulaSignSlotRadialBranchCuts.cuts
      (FormulaSignSlotRadialJointStratumLabels.source true c) (center c x)) :
    ∃ i : Vertex (CanonicalAuxiliaryCandidateCover.width (FormulaSignSlotRadialJointStratumLabels.source false c)),
    ∃ j : Vertex (CanonicalAuxiliaryCandidateCover.width (FormulaSignSlotRadialJointStratumLabels.source true c)),
      i.val = FormulaSignSlotRadialJointStratumLabels.label false c ∧
      j.val = FormulaSignSlotRadialJointStratumLabels.label true c ∧
      (FormulaSignSlotCircularBoundedCover.projectedPoint
        (FormulaSignSlotRadialJointStratumLabels.source false c)
        (FormulaSignSlotRadialJointStratumLabels.project false c x)).val ∈
          FormulaSignSlotRadialAccess.projectedPiece (FormulaSignSlotRadialJointStratumLabels.source false c)
            ((CanonicalAuxiliaryCandidateLabelLock.positiveCover
              (FormulaSignSlotRadialJointStratumLabels.source false c)).piece i) ∧
      FormulaSignSlotRadialJointRealization.leftCenter (FormulaSignSlotRadialJointStratum.header c)
        (FormulaSignSlotRadialJointStratumLabels.project false c x) ∈
          closure (FormulaSignSlotRadialAccess.projectedPiece (FormulaSignSlotRadialJointStratumLabels.source true c)
            ((CanonicalAuxiliaryCandidateLabelLock.positiveCover
              (FormulaSignSlotRadialJointStratumLabels.source true c)).piece j)) := by
  obtain ⟨i,hi,HM⟩ := atLabel_closed_mem false c x (h false)
  obtain ⟨hj,HP⟩ := h true
  let j := labelVertex true c hj
  refine ⟨i,j,hi,rfl,?_,?_⟩
  · exact FormulaSignSlotCircularBoundedCover.projectedPoint_mem _
      (CanonicalAuxiliaryCandidateCover.closedCover _).piece
      (CanonicalAuxiliaryCandidateCover.closedCover _).cover
      (CanonicalAuxiliaryCandidateCover.closed_accessible _) i _ HM
  · rw [← center_left_projection]
    exact (descriptor c x j (labelVertex_good true c hj)
      (by rwa [closedSample_eq]) hg hc).mem_projected_closure

end LeanCanny.Connectivity.FormulaSignSlotRadialJointClosureGeometry
