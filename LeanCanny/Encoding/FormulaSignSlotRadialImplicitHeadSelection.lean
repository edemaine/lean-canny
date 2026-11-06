/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitHeadWindow
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitGridSelection
/-! # Finite native selection of actual leading and trailing radius heads -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitHeadSelection
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input

def selectedQuery (z:List Bool):=FormulaSignSlotRadialImplicitGridSelection.selectedQuery z
def windowQuery (z:List Bool):=pair (pairFst (pairFst z)) (pair (pairSnd (pairFst z)) (pairSnd z))
theorem selectedQuery_FP:selectedQuery∈FP:=FormulaSignSlotRadialImplicitGridSelection.selectedQuery_FP
theorem windowQuery_FP:windowQuery∈FP:=by polytime [windowQuery]
noncomputable def Candidate (z:List Bool):Prop:=
  FormulaSignSlotRadialImplicitCenterSelection.Guards (selectedQuery z) ∧
    FormulaSignSlotRadialImplicitHeadWindow.Empty (windowQuery (selectedQuery z))
theorem candidate_evaluator:SpaceFunction (fun z=>[decide (Candidate z)]):=by
  have EC:=FormulaSignSlotRadialImplicitCenterSelection.evaluator.precompose selectedQuery selectedQuery_FP
  have EW:=FormulaSignSlotRadialImplicitHeadWindow.empty_evaluator.precompose
    (windowQuery∘selectedQuery) (mem_FP_comp selectedQuery_FP windowQuery_FP)
  exact (EC.andFlags EW).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Candidate,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq])
noncomputable abbrev limit:=FormulaSignSlotRadialImplicitGridSelection.limit
noncomputable def Leading (p:List Bool):Prop:=∃tau<limit p,∃D<limit p,
  Candidate (pair (pair p (BinaryNatCode.encode tau)) (BinaryNatCode.encode D))
theorem leading_evaluator:SpaceFunction (fun p=>[decide (Leading p)]):=by
  have HD:BinaryFn (fun z=>limit (pairFst z)):=FormulaSignSlotRadialImplicitGridSelection.limit_binary.comp pairFst_mem_FP
  have ED:=candidate_evaluator.exists_binary HD
  have ET:=ED.exists_binary FormulaSignSlotRadialImplicitGridSelection.limit_binary
  exact ET.congr (funext fun p=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Leading,List.cons.injEq,and_true,decide_eq_true_eq,pairFst_pair])

noncomputable abbrev radiusContext:=FormulaSignSlotRadialImplicitHeadWindow.radiusContext
noncomputable abbrev center:=FormulaSignSlotRadialImplicitHeadWindow.center
noncomputable abbrev bound:=FormulaSignSlotRadialImplicitHeadWindow.bound

theorem limit_packet (c w:List Bool) (j:ℕ):limit (pair (pair c w) (BinaryNatCode.encode j))=
    FormulaSignSlotRadialCenterSelection.bound (radiusContext c j)+1:=by
  simp only [limit,FormulaSignSlotRadialImplicitGridSelection.limit,FormulaSignSlotRadialImplicitGridSelection.context,pairFst_pair]
  unfold FormulaSignSlotRadialJointCoefficientCatalogue.limit
  apply congrArg (fun n=>n+1)
  apply FormulaSignSlotRadialEliminantRootProfiles.degree_eq
  simp only [FormulaSignSlotRadialJointCoefficientCatalogue.base,FormulaSignSlotRadialCoordinatePacket.root,
    FormulaSignSlotRadialImplicitHeadWindow.radiusContext,pairFst_pair]

private theorem selected_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j tau D:ℕ):
    FormulaSignSlotRadialImplicitCenterSelection.Guards
      (FormulaSignSlotRadialImplicitCenterSelection.packet c w j tau D)↔
    FormulaSignSlotRadialCenterSelection.Guards (radiusContext c j) (center c w hw j) tau D:=by
  exact FormulaSignSlotRadialImplicitCenterSelection.guards_packet c w hw j tau D

private theorem candidate_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w)
    (j tau D:ℕ) (hb:0<bound c w hw):
    Candidate (pair (pair (pair (pair c w) (BinaryNatCode.encode j)) (BinaryNatCode.encode tau)) (BinaryNatCode.encode D))↔
      FormulaSignSlotRadialCenterSelection.Guards (radiusContext c j) (center c w hw j) tau D ∧
      ∀r,(FormulaSignSlotRadialRadiusHeadInterval.specialized (radiusContext c j) (center c w hw j) tau D).eval r=0 → r ∉ Ioo 0 (bound c w hw):=by
  have HS:selectedQuery (pair (pair (pair (pair c w) (BinaryNatCode.encode j)) (BinaryNatCode.encode tau)) (BinaryNatCode.encode D))=
    FormulaSignSlotRadialImplicitCenterSelection.packet c w j tau D:=by
    simp only [selectedQuery,FormulaSignSlotRadialImplicitGridSelection.selectedQuery,
      FormulaSignSlotRadialImplicitCenterSelection.packet,pairFst_pair,pairSnd_pair]
  have HW:windowQuery (FormulaSignSlotRadialImplicitCenterSelection.packet c w j tau D)=
    FormulaSignSlotRadialImplicitHeadWindow.packet c w j tau D:=by
    simp only [windowQuery,FormulaSignSlotRadialImplicitCenterSelection.packet,
      FormulaSignSlotRadialImplicitHeadWindow.packet,pairFst_pair,pairSnd_pair]
  rw [Candidate,HS,HW,selected_packet,FormulaSignSlotRadialImplicitHeadWindow.empty_packet_iff c w hw j tau D hb]

private theorem leading_eq (c:List Bool) (a:Fin (FormulaSignSlotRadialRadiusWindowSigns.centerCount c)→ℝ)
    (tau D:ℕ) (h:FormulaSignSlotRadialCenterSelection.Guards c a tau D):
    FormulaSignSlotRadialRadiusHeadInterval.specialized c a tau D=
      (FormulaSignSlotRadialCenterSquarefreeSelection.coordinate c a).leadingCoeff:=
  FormulaSignSlotRadialRadiusHeadEvaluation.leading c a tau D h

attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialCenterSquarefreeSelection.coordinate
  FormulaSignSlotRadialImplicitHeadWindow.radiusContext FormulaSignSlotRadialImplicitHeadWindow.center
  FormulaSignSlotRadialImplicitHeadWindow.bound

/-- The perturbation and target degree are searched and verified on this OWN word. -/
theorem leading_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w)
    (j:ℕ) (hb:0<bound c w hw):
    Leading (pair (pair c w) (BinaryNatCode.encode j))↔
      ∀r,(FormulaSignSlotRadialCenterSquarefreeSelection.coordinate (radiusContext c j)
        (center c w hw j)).leadingCoeff.eval r=0 → r ∉ Ioo 0 (bound c w hw):=by
  constructor
  · rintro ⟨tau,_,D,_,HC⟩
    obtain ⟨HG,HN⟩:=(candidate_packet_iff c w hw j tau D hb).mp HC
    rw [leading_eq _ _ _ _ HG] at HN
    exact HN
  · intro H
    obtain ⟨tau,ht,D,hD,HG⟩:=FormulaSignSlotRadialCenterSelection.exists_guards (radiusContext c j) (center c w hw j)
    refine ⟨tau,?_,D,?_,(candidate_packet_iff c w hw j tau D hb).mpr ⟨HG,?_⟩⟩
    · rw [limit_packet];omega
    · rw [limit_packet];omega
    · rw [leading_eq _ _ _ _ HG]
      exact H

end LeanCanny.Encoding.FormulaSignSlotRadialImplicitHeadSelection
