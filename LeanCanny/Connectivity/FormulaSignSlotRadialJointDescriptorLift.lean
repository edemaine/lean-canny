/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratumReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialJointRealization
public import LeanCanny.Connectivity.FormulaSignSlotRadialJointClosureGeometry
/-! # A genuine radial descriptor lifts to the actual joint stratum

The internally chosen zero count and reciprocal witness retain both closed
lifts, the anchor grid and the complete cut-free interval.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialJointDescriptorLift
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.ETR
open FormulaSignSlotRadialJointDescriptorGeometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem closed_eq (side : Bool) (u : List Bool) (env : ℕ → ℝ)
    (h : (FormulaSignSlotRadialJointCore.equation u).eval env = 0)
    (A : FormulaSignSlotCircularBoundedCover.Source (FormulaSignSlotRadialJointLayout.source side u))
    (ha : ∀ j : Fin (FormulaSignSlotRadialJointLayout.circleCount side u),
      env (FormulaSignSlotRadialJointLayout.column (if side then 1 else 0) j.val) = A.val j) :
    FormulaSignSlotRadialJointGeometry.closedPoint side u env h = A := by
  apply Subtype.ext
  funext j
  exact ha j

private theorem atLabel_of_projection (side : Bool) (c u : List Bool)
    (hu : FormulaSignSlotRadialJointStratumLabels.source side c = u)
    (x : FormulaSignSlotRadialJointStratumLabels.Space c)
    (A : FormulaSignSlotCircularBoundedCover.Source u)
    (i : Vertex (CanonicalAuxiliaryCandidateCover.width u))
    (hi : i.val = FormulaSignSlotRadialJointStratumLabels.label side c)
    (hm : A ∈ (CanonicalAuxiliaryCandidateCover.closedCover u).piece i)
    (hx : HEq (FormulaSignSlotRadialJointStratumLabels.project side c x) A) :
    FormulaSignSlotRadialJointStratumLabels.AtLabel side c x := by
  subst u
  apply (FormulaSignSlotRadialJointClosureGeometry.atLabel_iff_closed_mem side c x).mpr
  refine ⟨i,hi,?_⟩
  rw [eq_of_heq hx]
  exact hm

theorem exists_lift (H : List Bool)
    (A : FormulaSignSlotCircularBoundedCover.Source (FormulaSignSlotRadialJointLayout.source false H))
    (i : Vertex (CanonicalAuxiliaryCandidateCover.width (FormulaSignSlotRadialJointLayout.source true H)))
    (D : FormulaSignSlotCandidateRadialDescriptor.Descriptor (FormulaSignSlotRadialJointLayout.source true H)
      i (FormulaSignSlotRadialJointRealization.leftCenter H A)) :
    ∃ k ≤ FormulaSignSlotRadialJointCoefficientCatalogue.family.count H,
    ∃ y : FormulaSignSlotRadialJointStratumLabels.Space (FormulaSignSlotRadialJointStratum.packet H k),
      HEq (FormulaSignSlotRadialJointStratumLabels.project false _ y) A ∧
      HEq (FormulaSignSlotRadialJointStratumLabels.project true _ y) D.closedAnchor ∧
      (anchor _ y).val.val ∈ FormulaSignSlotRadialParameterGrid.grid
        (FormulaSignSlotRadialJointStratumLabels.source true _) (center _ y) (radius _ y) ∧
      ∀ t ∈ Set.Ioo 0 (bound _ y), t ∉ FormulaSignSlotRadialBranchCuts.cuts
        (FormulaSignSlotRadialJointStratumLabels.source true _) (center _ y) := by
  obtain ⟨env,h0,hA,hB,_,_,_,_,hG,hC⟩ :=
    FormulaSignSlotRadialJointRealization.exists_root_of_descriptor H A i D
  let x := FormulaSignSlotRadialJointCorePoint.ofEnvironment H env h0
  obtain ⟨k,hk,y,hy⟩ := FormulaSignSlotRadialJointStratumLift.exists_lift H x
  let c := FormulaSignSlotRadialJointStratum.packet H k
  have HC : FormulaSignSlotRadialJointStratum.header c = H := LeanCanny.pairFst_pair _ _
  have HA := FormulaSignSlotRadialJointStratumLift.project_heq false c H HC y x hy
  have HB := FormulaSignSlotRadialJointStratumLift.project_heq true c H HC y x hy
  have HCA := (FormulaSignSlotRadialJointCorePoint.project_ofEnvironment false H env h0).trans
    (closed_eq false H env h0 A hA)
  have HCB := (FormulaSignSlotRadialJointCorePoint.project_ofEnvironment true H env h0).trans
    (closed_eq true H env h0 D.closedAnchor hB)
  refine ⟨k,hk,y,HA.trans (heq_of_eq HCA),HB.trans (heq_of_eq HCB),?_,?_⟩
  · exact (FormulaSignSlotRadialJointStratumReadback.grid_iff c H HC env h0 y hy).mpr hG
  · exact (FormulaSignSlotRadialJointStratumReadback.cut_free_iff c H HC env h0 y hy).mpr hC

theorem exists_labelled_lift (H : List Bool)
    (A : FormulaSignSlotCircularBoundedCover.Source (FormulaSignSlotRadialJointLayout.source false H))
    (i : Vertex (CanonicalAuxiliaryCandidateCover.width (FormulaSignSlotRadialJointLayout.source true H)))
    (D : FormulaSignSlotCandidateRadialDescriptor.Descriptor (FormulaSignSlotRadialJointLayout.source true H)
      i (FormulaSignSlotRadialJointRealization.leftCenter H A))
    (j : Vertex (CanonicalAuxiliaryCandidateCover.width (FormulaSignSlotRadialJointLayout.source false H)))
    (hj : j.val = CanonicalAuxiliaryCandidateLabels.candidate (FormulaSignSlotRadialJointLayout.labelQuery false H))
    (hi : i.val = CanonicalAuxiliaryCandidateLabels.candidate (FormulaSignSlotRadialJointLayout.labelQuery true H))
    (hA : A ∈ (CanonicalAuxiliaryCandidateCover.closedCover (FormulaSignSlotRadialJointLayout.source false H)).piece j) :
    ∃ k ≤ FormulaSignSlotRadialJointCoefficientCatalogue.family.count H,
    ∃ y : FormulaSignSlotRadialJointStratumLabels.Space (FormulaSignSlotRadialJointStratum.packet H k),
      FormulaSignSlotRadialJointStratumLabels.BothLabels _ y ∧
      (anchor _ y).val.val ∈ FormulaSignSlotRadialParameterGrid.grid
        (FormulaSignSlotRadialJointStratumLabels.source true _) (center _ y) (radius _ y) ∧
      ∀ t ∈ Set.Ioo 0 (bound _ y), t ∉ FormulaSignSlotRadialBranchCuts.cuts
        (FormulaSignSlotRadialJointStratumLabels.source true _) (center _ y) := by
  obtain ⟨k,hk,y,hL,hR,hG,hC⟩ := exists_lift H A i D
  let c := FormulaSignSlotRadialJointStratum.packet H k
  have HC : FormulaSignSlotRadialJointStratum.header c = H := LeanCanny.pairFst_pair _ _
  have HS (side : Bool) : FormulaSignSlotRadialJointStratumLabels.source side c =
      FormulaSignSlotRadialJointLayout.source side H := congrArg (FormulaSignSlotRadialJointLayout.source side) HC
  have HL (side : Bool) : FormulaSignSlotRadialJointStratumLabels.label side c =
      CanonicalAuxiliaryCandidateLabels.candidate (FormulaSignSlotRadialJointLayout.labelQuery side H) :=
    congrArg (fun u => CanonicalAuxiliaryCandidateLabels.candidate
      (FormulaSignSlotRadialJointLayout.labelQuery side u)) HC
  have HRMem : D.closedAnchor ∈ (CanonicalAuxiliaryCandidateCover.closedCover
      (FormulaSignSlotRadialJointLayout.source true H)).piece i :=
    (CanonicalAuxiliaryCandidateLabelLock.closed_mem_iff _ _ _).mpr ⟨D.good,D.anchor_component⟩
  refine ⟨k,hk,y,?_,hG,hC⟩
  intro side
  cases side
  · exact atLabel_of_projection false c _ (HS false) y A j (hj.trans (HL false).symm) hA hL
  · exact atLabel_of_projection true c _ (HS true) y D.closedAnchor i (hi.trans (HL true).symm) HRMem hR

end LeanCanny.Connectivity.FormulaSignSlotRadialJointDescriptorLift
