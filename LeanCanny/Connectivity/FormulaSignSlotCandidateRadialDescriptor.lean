/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryCandidateLabelLock
public import LeanCanny.Connectivity.FormulaSignSlotProjectedPieceAccess
/-! # Finite real radial data retain the actual selected component

No curve is a descriptor field. The actual finite parameter grid and cut-free
interval determine a branch internally; its positive anchor locks the same
candidate component. These are real receipts, with no algebraic word bound.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotCandidateRadialDescriptor
open ETR Set Filter Polynomial LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Algebra
open FormulaSignSlotMarginProjection FormulaSignSlotComponentMaxima
open FormulaSignSlotCenteredRadialGraph FormulaSignSlotCenteredRadialLimits
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialParameterPolynomial.polynomial degreeBudget
  FormulaSignSlotMargin.initialDimension FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialPolynomial
  FormulaSignSlotTiltedRadialGrid.Q CanonicalAuxiliaryCandidateCover.dimension CanonicalAuxiliaryCandidateCover.equation
  CanonicalAuxiliaryCandidateCover.width CanonicalAuxiliaryCandidateLabelLock.Good
  CanonicalAuxiliaryCandidateLabelLock.positiveProjection CanonicalAuxiliaryCandidateLabelLock.closedSample
  FormulaSignSlotCircularBoundedCover.root FormulaSignSlotCircularInterior.description
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom
  ClosedFormulaGateMetadata.kind Input.field FormulaView.normalize

structure Descriptor (c :List Bool) (i :Vertex (CanonicalAuxiliaryCandidateCover.width c))
    (center :Fin (d c)→ℝ) where
  bound :ℝ
  bound_pos :0<bound
  parameter :Ioo (0:ℝ) bound
  anchor :FormulaSignSlotTiltedRadialGrid.OldPositive c center parameter.val
  grid :anchor.val.val∈FormulaSignSlotRadialParameterGrid.grid c center parameter.val
  cut_free :∀t∈Ioo 0 bound,t∉FormulaSignSlotRadialBranchCuts.cuts c center
  good :CanonicalAuxiliaryCandidateLabelLock.Good c i
  closedAnchor :FormulaSignSlotCircularBoundedCover.Source c
  anchor_projection :CanonicalAuxiliaryCandidateLabelLock.positiveProjection c closedAnchor=
    FormulaSignSlotTiltedRadialGrid.originalPositive c center parameter.val anchor
  anchor_component :JoinedIn univ (CanonicalAuxiliaryCandidateLabelLock.closedSample c i good) closedAnchor

namespace Descriptor
variable {c :List Bool} {i :Vertex (CanonicalAuxiliaryCandidateCover.width c)}
  {center :Fin (d c)→ℝ} (D :Descriptor c i center)

theorem finite_anchor_grid :(FormulaSignSlotRadialParameterGrid.grid c center D.parameter.val).Finite:=
  FormulaSignSlotRadialParameterGrid.finite_grid c center D.parameter.val
    (FormulaSignSlotRadialBranchCuts.conditions c center _ (D.cut_free _ D.parameter.property)).1

theorem selected_curve :∃f :C(Ioo (0:ℝ) D.bound,Positive c),
    f D.parameter=FormulaSignSlotTiltedRadialGrid.originalPositive c center D.parameter.val D.anchor ∧
    ∀t,SquaredDistanceFibers.value center (projection c (f t).val).val=t.val:=by
  obtain ⟨_,curve,_,HG,HC⟩:=FormulaSignSlotRadialBranchCuts.branches c center D.bound D.parameter D.cut_free
  obtain ⟨j,HJ,_⟩:=(HC D.parameter D.anchor.val.val).mp D.grid
  exact FormulaSignSlotRadialBranchSelection.selected_curve c center D.bound D.cut_free D.parameter
    D.anchor (curve j) HJ (HG j)

theorem source_branch :∃F :ℝ→Source c,
    ContinuousOn F (Ioo 0 D.bound) ∧
    (∀t∈Ioo 0 D.bound,0<value c (F t)) ∧
    (∀t∈Ioo 0 D.bound,SquaredDistanceFibers.value center (projection c (F t)).val=t) ∧
    ∀t∈Ioo 0 D.bound,F t∈ambient c ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i):=by
  obtain ⟨f,HA,HD⟩:=D.selected_curve
  let F :ℝ→Source c:=fun t=>if ht:t∈Ioo 0 D.bound then (f ⟨t,ht⟩).val else
    (FormulaSignSlotTiltedRadialGrid.originalPositive c center D.parameter.val D.anchor).val
  have HE (t :Ioo (0:ℝ) D.bound):F t.val=(f t).val:=by
    simp only [F,dite_eq_left t.property]
  have HF:ContinuousOn F (Ioo 0 D.bound):=by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp f.continuous using 1
    funext t
    exact HE t
  have HP (t :ℝ) (ht:t∈Ioo 0 D.bound):0<value c (F t):=by
    rw [HE ⟨t,ht⟩]
    exact (f ⟨t,ht⟩).property
  have HR (t :ℝ) (ht:t∈Ioo 0 D.bound):
      SquaredDistanceFibers.value center (projection c (F t)).val=t:=by
    rw [HE ⟨t,ht⟩]
    exact HD ⟨t,ht⟩
  have HL:FormulaSignSlotTiltedRadialGrid.originalPositive c center D.parameter.val D.anchor∈
      (CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i:=
    (CanonicalAuxiliaryCandidateLabelLock.positive_mem_iff c i _).mpr
      ⟨D.good,D.closedAnchor,D.anchor_projection,D.anchor_component⟩
  have HI:F D.parameter.val∈ambient c ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i):=by
    rw [HE D.parameter,HA]
    exact ⟨_,HL,rfl⟩
  exact ⟨F,HF,HP,HR,FormulaSignSlotRadialAccess.arc_label c
    (CanonicalAuxiliaryCandidateLabelLock.positiveCover c) i D.bound F HF HP
      D.parameter.val D.parameter.property HI⟩

include D in
theorem mem_projected_closure :center∈closure (FormulaSignSlotRadialAccess.projectedPiece c
    ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i)):=by
  obtain ⟨F,_,_,HR,HC⟩:=D.source_branch
  have HT:=RadialArcAccess.tendsto_center center D.bound D.bound_pos
    (fun t=>(projection c (F t)).val) HR
  apply mem_closure_of_tendsto HT
  filter_upwards [Ioo_mem_nhdsGT D.bound_pos] with t ht
  exact ⟨F t,HC t ht,rfl⟩
end Descriptor

theorem exists_of_projected_boundary (c :List Bool) (i :Vertex (CanonicalAuxiliaryCandidateCover.width c))
    (center :Fin (d c)→ℝ)
    (hx :center∈closure (FormulaSignSlotRadialAccess.projectedPiece c
      ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i)))
    (hn :center∉FormulaSignSlotRadialAccess.projectedPiece c
      ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i)):
    Nonempty (Descriptor c i center):=by
  let C:=(CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i
  obtain ⟨x,HX,HP⟩:=FormulaSignSlotProjectedPieceAccess.boundary_lift c C center hx
  have HN:x∉ambient c C:=fun h=>hn ⟨x,h,HP⟩
  subst center
  obtain ⟨r0,_,_,HB0,z0,_,HG0,_⟩:=FormulaSignSlotRadialParameterGrid.arbitrarily_small_samples
    c C ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).clopen i) x HX HN 1 zero_lt_one
  obtain ⟨b,hb,HB⟩:=FormulaSignSlotRadialBranchCuts.small_interval c (projection c x).val r0 HB0 z0.val.val HG0
  obtain ⟨r,hr,hl,_,z,HZ,HG,_⟩:=FormulaSignSlotRadialParameterGrid.arbitrarily_small_samples
    c C ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).clopen i) x HX HN b hb
  obtain ⟨hi,lift,HL,HJ⟩:=(CanonicalAuxiliaryCandidateLabelLock.positive_mem_iff c i _).mp HZ
  exact ⟨{
    bound:=b
    bound_pos:=hb
    parameter:=⟨r,hr,hl⟩
    anchor:=z
    grid:=HG
    cut_free:=HB
    good:=hi
    closedAnchor:=lift
    anchor_projection:=HL
    anchor_component:=HJ
  }⟩

theorem projected_closure_iff (c :List Bool) (i :Vertex (CanonicalAuxiliaryCandidateCover.width c))
    (center :Fin (d c)→ℝ):
    center∈closure (FormulaSignSlotRadialAccess.projectedPiece c
      ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i)) ↔
    center∈FormulaSignSlotRadialAccess.projectedPiece c
      ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i) ∨Nonempty (Descriptor c i center):=by
  constructor
  · intro H
    by_cases HM:center∈FormulaSignSlotRadialAccess.projectedPiece c
        ((CanonicalAuxiliaryCandidateLabelLock.positiveCover c).piece i)
    · exact Or.inl HM
    · exact Or.inr (exists_of_projected_boundary c i center H HM)
  · intro H
    rcases H with HM|HD
    · exact subset_closure HM
    · exact HD.elim (fun D=>Descriptor.mem_projected_closure D)

end LeanCanny.Connectivity.FormulaSignSlotCandidateRadialDescriptor
