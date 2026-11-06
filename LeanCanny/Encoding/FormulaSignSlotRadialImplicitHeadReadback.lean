/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitTrailingSelection
/-! # Native head and margin intervals at literal coordinates of one own sample -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitHeadReadback
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input

noncomputable def root (c:List Bool):=FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialImplicitGridTest.header c)
theorem root_FP:root∈FP:=mem_FP_comp (f:=FormulaSignSlotRadialImplicitGridTest.header)
  (g:=FormulaSignSlotRadialJointLayout.source true) FormulaSignSlotRadialImplicitGridTest.header_FP
  (FormulaSignSlotRadialJointLayout.source_FP true)
noncomputable def center (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w):
    Fin (FormulaSignSlotCenteredRadialGraph.d (root c))→ℝ:=
  fun i=>FormulaSignSlotRadialImplicitSourceTest.env c w hw (4*i.val)
noncomputable abbrev bound:=FormulaSignSlotRadialImplicitHeadWindow.bound
noncomputable def coordinate (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w):=
  FormulaSignSlotRadialParameterEliminant.coordinate (root c) (center c w hw)

private theorem natural_point_heq {n m:ℕ} (h:n=m) (v:ℕ→ℝ):
    HEq (fun i:Fin n=>v (4*i.val)) (fun i:Fin m=>v (4*i.val)):=by cases h;rfl
private theorem coordinate_transport (u v:List Bool) (hu:u=v)
    (a:Fin (FormulaSignSlotCenteredRadialGraph.d u)→ℝ) (b:Fin (FormulaSignSlotCenteredRadialGraph.d v)→ℝ) (hab:HEq a b)
    (i:Fin (FormulaSignSlotCenteredRadialGraph.N u+FormulaSignSlotCenteredRadialGraph.d u+1))
    (j:Fin (FormulaSignSlotCenteredRadialGraph.N v+FormulaSignSlotCenteredRadialGraph.d v+1)) (hij:i.val=j.val):
    FormulaSignSlotRadialParameterEliminant.coordinate u a i=FormulaSignSlotRadialParameterEliminant.coordinate v b j:=by
  cases hu
  cases eq_of_heq hab
  have H:i=j:=Fin.ext hij
  rw [H]
private theorem packet_center (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (j:ℕ):
    FormulaSignSlotRadialImplicitHeadWindow.center c w hw j=
      (fun i:Fin (FormulaSignSlotCenteredRadialGraph.d (pairFst (FormulaSignSlotRadialImplicitHeadWindow.radiusContext c j)))=>
        FormulaSignSlotRadialImplicitSourceTest.env c w hw (4*i.val)):=rfl
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialParameterEliminant.coordinate

/-- No zero-set, selection or compatibility receipt is required for this column identity. -/
theorem coordinate_packet (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialImplicitGridTest.header c))):
    FormulaSignSlotRadialCenterSquarefreeSelection.coordinate
      (FormulaSignSlotRadialImplicitHeadWindow.radiusContext c j.val)
      (FormulaSignSlotRadialImplicitHeadWindow.center c w hw j.val)=coordinate c w hw j:=by
  let r:=FormulaSignSlotRadialImplicitHeadWindow.radiusContext c j.val
  have HC:pairFst r=root c:=FormulaSignSlotRadialCoordinatePacket.root (root c) j.val
  have HA:=natural_point_heq (congrArg FormulaSignSlotCenteredRadialGraph.d HC) (FormulaSignSlotRadialImplicitSourceTest.env c w hw)
  have HAB:HEq (FormulaSignSlotRadialImplicitHeadWindow.center c w hw j.val) (center c w hw):=
    (heq_of_eq (packet_center c w hw j.val)).trans HA
  have HI:(FormulaSignSlotRadialEliminantInput.coordinate r).val=j.val:=by
    change (FormulaSignSlotRadialEliminantInput.coordinate (FormulaSignSlotRadialCoordinatePacket.packet (root c) j.val)).val=j.val
    rw [FormulaSignSlotRadialCoordinatePacket.selected]
    exact Nat.min_eq_left (by have H:=j.isLt;change j.val<FormulaSignSlotCenteredRadialGraph.N (root c)+FormulaSignSlotCenteredRadialGraph.d (root c)+1 at H;omega)
  exact coordinate_transport _ _ HC _ _ HAB _ j HI

theorem leading_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialImplicitGridTest.header c))) (hb:0<bound c w hw):
    FormulaSignSlotRadialImplicitHeadSelection.Leading (pair (pair c w) (BinaryNatCode.encode j.val))↔
      ∀r,(coordinate c w hw j).leadingCoeff.eval r=0 → r ∉ Ioo 0 (bound c w hw):=by
  have H:=FormulaSignSlotRadialImplicitHeadSelection.leading_packet_iff c w hw j.val hb
  rw [coordinate_packet] at H
  exact H

theorem trailing_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialImplicitGridTest.header c))) (hb:0<bound c w hw):
    FormulaSignSlotRadialImplicitTrailingSelection.At (pair (pair c w) (BinaryNatCode.encode j.val))↔
      ∀r,(coordinate c w hw j).trailingCoeff.eval r=0 → r ∉ Ioo 0 (bound c w hw):=by
  have H:=FormulaSignSlotRadialImplicitTrailingSelection.at_packet_iff c w hw j.val hb
  rw [coordinate_packet] at H
  exact H

noncomputable def margin (c:List Bool):=FormulaSignSlotMargin.objective (root c)
theorem margin_unary:UnaryFn margin:=FormulaSignSlotMargin.objective_unary.comp root_FP
noncomputable def marginQuery (p:List Bool):=pair p (BinaryNatCode.encode (margin (pairFst p)))
theorem marginQuery_FP:marginQuery∈FP:=mem_FP_pair id_mem_FP
  (BinaryFn.ofUnary (margin_unary.comp pairFst_mem_FP)).bits_mem_FP
private theorem marginQuery_packet (c w:List Bool):marginQuery (pair c w)=
    pair (pair c w) (BinaryNatCode.encode (FormulaSignSlotCenteredRadialGraph.marginIndex (root c)).val):=by
  simp only [marginQuery,pairFst_pair]
  rfl
noncomputable def Holds (p:List Bool):Prop:=FormulaSignSlotRadialImplicitTrailingSelection.At (marginQuery p)
theorem evaluator:SpaceFunction (fun p=>[decide (Holds p)]):=
  FormulaSignSlotRadialImplicitTrailingSelection.at_evaluator.precompose marginQuery marginQuery_FP

theorem holds_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (hb:0<bound c w hw):
    Holds (pair c w)↔∀r,(coordinate c w hw (FormulaSignSlotCenteredRadialGraph.marginIndex (root c))).trailingCoeff.eval r=0 → r ∉ Ioo 0 (bound c w hw):=by
  unfold Holds
  rw [marginQuery_packet]
  exact trailing_packet_iff c w hw (FormulaSignSlotCenteredRadialGraph.marginIndex (root c)) hb

noncomputable def language:Language:={p|SquareSampleCompleteVertices.Valid F (pairFst p) (pairSnd p) ∧Holds p}
theorem decider:SpaceDecider language:=by
  have EV:=SquareSampleCompleteVertices.decider (ImplicitSourceGramGrid.access FormulaSignSlotRadialJointStratum.source
    FormulaSignSlotRadialJointStratumNative.access FormulaSignSlotRadialJointStratumSampler.positive)
  apply (EV.flagEvaluator.andFlags evaluator).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro p
  simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE:language∈PSPACE:=decider.mem_PSPACE

theorem language_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (hb:0<bound c w hw):
    pair c w∈language↔∀r,(coordinate c w hw (FormulaSignSlotCenteredRadialGraph.marginIndex (root c))).trailingCoeff.eval r=0 → r ∉ Ioo 0 (bound c w hw):=by
  simp only [language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,hw,true_and]
  exact holds_packet_iff c w hw hb

end LeanCanny.Encoding.FormulaSignSlotRadialImplicitHeadReadback
