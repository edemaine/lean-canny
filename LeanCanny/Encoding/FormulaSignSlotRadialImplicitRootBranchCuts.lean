/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitBranchCutTest
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitHeadSelection
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCoreReadback
/-! # The whole actual root-branch cut checker on one accepted implicit word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitRootBranchCuts
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.ETR Polynomial Set
open scoped Classical
open Brackets
set_option backward.isDefEq.respectTransparency false
local notation "F"=>FormulaSignSlotRadialJointStratumSampler.input
local notation "env"=>FormulaSignSlotRadialImplicitSourceTest.env
local notation "original"=>FormulaSignSlotRadialImplicitPrincipalWindow.original
attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialParameterEliminant.coordinate

noncomputable def Each (q:List Bool):Prop:=FormulaSignSlotRadialImplicitHeadSelection.Leading q ∧
  FormulaSignSlotRadialImplicitBranchCutTest.At q
theorem each_evaluator:SpaceFunction (fun q=>[decide (Each q)]):=
  IntegralPolynomialWindowTarskiDecision.flag_and _ _ FormulaSignSlotRadialImplicitHeadSelection.leading_evaluator
    FormulaSignSlotRadialImplicitBranchCutTest.at_evaluator
noncomputable def count (p:List Bool):=FormulaSignSlotRadialJointLayout.spatialCount
  (FormulaSignSlotRadialImplicitGridTest.header (pairFst p))
theorem count_unary:UnaryFn count:=FormulaSignSlotRadialJointLayout.spatialCount_unary.comp
  (mem_FP_comp (f:=pairFst) (g:=FormulaSignSlotRadialImplicitGridTest.header)
    pairFst_mem_FP FormulaSignSlotRadialImplicitGridTest.header_FP)
noncomputable def Holds (p:List Bool):Prop:=∀j<count p,Each (pair p (BinaryNatCode.encode j))
theorem holds_evaluator:SpaceFunction (fun p=>[decide (Holds p)]):=
  (each_evaluator.forall_binary (BinaryFn.ofUnary count_unary)).congr (funext fun p=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Holds,List.cons.injEq,and_true,decide_eq_true_eq])

private theorem natural_heq {n m:ℕ} (h:n=m) (v:ℕ→ℝ):
    HEq (fun i:Fin n=>v (4*i.val)) (fun i:Fin m=>v (4*i.val)):=by cases h;rfl
private theorem coordinate_transport (u v:List Bool) (hu:u=v)
    (a:Fin (FormulaSignSlotCenteredRadialGraph.d u)→ℝ) (b:Fin (FormulaSignSlotCenteredRadialGraph.d v)→ℝ)
    (hab:HEq a b)
    (i:Fin (FormulaSignSlotCenteredRadialGraph.N u+FormulaSignSlotCenteredRadialGraph.d u+1))
    (j:Fin (FormulaSignSlotCenteredRadialGraph.N v+FormulaSignSlotCenteredRadialGraph.d v+1)) (hi:i.val=j.val):
    FormulaSignSlotRadialParameterEliminant.coordinate u a i=FormulaSignSlotRadialParameterEliminant.coordinate v b j:=by
  cases hu
  cases eq_of_heq hab
  rw [Fin.ext hi]
theorem row_count (c:List Bool):FormulaSignSlotRadialJointLayout.spatialCount
    (FormulaSignSlotRadialImplicitGridTest.header c)=FormulaSignSlotCenteredRadialGraph.N (original c)+
      FormulaSignSlotCenteredRadialGraph.d (original c)+1:=rfl
noncomputable def rows (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w):
    Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialImplicitGridTest.header c))→Polynomial (Polynomial ℝ):=
  fun j=>FormulaSignSlotRadialParameterEliminant.coordinate (original c)
    (fun i=>env c w hw (4*i.val)) (Fin.cast (row_count c) j)
private theorem actual_coordinate (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialImplicitGridTest.header c))):
    FormulaSignSlotRadialImplicitBranchCutTest.coordinate c w hw j.val=rows c w hw j:=by
  unfold FormulaSignSlotRadialImplicitBranchCutTest.coordinate FormulaSignSlotRadialCenterSquarefreeSelection.coordinate rows
  have HC:=FormulaSignSlotRadialCoordinatePacket.root (original c) j.val
  apply coordinate_transport _ _ HC _ _ (natural_heq (congrArg FormulaSignSlotCenteredRadialGraph.d HC) (env c w hw))
  rw [FormulaSignSlotRadialCoordinatePacket.selected]
  exact Nat.min_eq_left (by have H:=j.isLt;change j.val<FormulaSignSlotCenteredRadialGraph.N (original c)+FormulaSignSlotCenteredRadialGraph.d (original c)+1 at H;omega)

theorem each_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w)
    (j:Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialImplicitGridTest.header c)))
    (hb:0<env c w hw 3):
    Each (pair (pair c w) (BinaryNatCode.encode j.val)) ↔
      RealParameterRootBranches.NoRoots (RealParameterRootBranches.cut (rows c w hw j)) (env c w hw 3):=by
  have HL:=FormulaSignSlotRadialImplicitHeadSelection.leading_packet_iff c w hw j.val hb
  change FormulaSignSlotRadialImplicitHeadSelection.Leading (pair (pair c w) (BinaryNatCode.encode j.val))↔
    RealParameterRootBranches.NoRoots (FormulaSignSlotRadialImplicitBranchCutTest.coordinate c w hw j.val).leadingCoeff (env c w hw 3) at HL
  rw [Each,HL]
  exact (FormulaSignSlotRadialImplicitBranchCutTest.cut_packet_iff c w hw j.val hb).symm.trans
    (iff_of_eq (congrArg (fun p=>RealParameterRootBranches.NoRoots (RealParameterRootBranches.cut p) (env c w hw 3))
      (actual_coordinate c w hw j)))

theorem holds_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (hb:0<env c w hw 3):
    Holds (pair c w) ↔ ∀r∈Ioo 0 (env c w hw 3),r ∉ RealParameterRootBranches.bad (rows c w hw):=by
  rw [RealParameterRootBranches.no_bad_iff]
  change (∀j<count (pair c w),Each (pair (pair c w) (BinaryNatCode.encode j)))↔_
  simp only [count,pairFst_pair]
  constructor
  · intro H j
    exact (each_packet_iff c w hw j hb).mp (H j.val j.isLt)
  · intro H j hj
    exact (each_packet_iff c w hw ⟨j,hj⟩ hb).mpr (H ⟨j,hj⟩)

private theorem restrict_environment {n:ℕ} (v:Fin (n+1)→ℝ) (i:Fin n):
    IntegralMixedFramedBankObservation.extend v i.val=Formula.extend (fun j:Fin n=>v j.castSucc) i.val:=by
  simp only [IntegralMixedFramedBankObservation.extend,Formula.extend,
    dite_eq_left i.isLt,dite_eq_left (i.isLt.trans (Nat.lt_succ_self n))]
  rfl

theorem bound_positive (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w)
    (hq:pair c w∈FormulaSignSlotRadialJointStratumSampler.language):0<env c w hw 3:=by
  let z:=SquareSampleCompleteVertices.candidate F c w hw
  let a:=Formula.extend (FormulaSignSlotRadialJointStratum.oldPoint (ImplicitSourceGramGrid.header c) z.val)
  have HC:=(FormulaSignSlotRadialJointStratumSampler.accepted_iff c w hw).mp hq |>.1
  have HP:=FormulaSignSlotRadialJointCoreReadback.parameter_positive
    (FormulaSignSlotRadialImplicitGridTest.header c) a HC
  have HI:3<FormulaSignSlotRadialJointStratum.oldArity (ImplicitSourceGramGrid.header c):=
    FormulaSignSlotRadialJointLayout.boundVariable_lt (FormulaSignSlotRadialImplicitGridTest.header c)
  have HE:=restrict_environment z.val ⟨3,HI⟩
  change env c w hw 3=a 3 at HE
  rw [HE]
  exact HP.1.trans HP.2

noncomputable def language:Language:={p|p∈FormulaSignSlotRadialJointStratumSampler.language ∧Holds p}
theorem decider:SpaceDecider language:=by
  have EV:=ImplicitSourceComponentSampler.decider FormulaSignSlotRadialJointStratum.source
    FormulaSignSlotRadialJointStratumNative.access FormulaSignSlotRadialJointStratumSampler.positive
  apply (EV.flagEvaluator.andFlags holds_evaluator).decider (fun v=>decide (v=[true]))
    (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro p
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE:language∈PSPACE:=decider.mem_PSPACE

/-- The filter and every branch cut refer to this one actual decoded word. -/
theorem language_packet_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w):
    pair c w∈language ↔ pair c w∈FormulaSignSlotRadialJointStratumSampler.language ∧
      ∀r∈Ioo 0 (env c w hw 3),r ∉ RealParameterRootBranches.bad (rows c w hw):=by
  change (pair c w∈FormulaSignSlotRadialJointStratumSampler.language ∧Holds (pair c w))↔_
  apply and_congr_right
  intro hq
  exact holds_packet_iff c w hw (bound_positive c w hw hq)

private theorem complete_valid (T:SquareSamplePolynomialTest.Test F) (s:SignType)
    (c w:List Bool) (hq:pair c w∈SquareSampleCompletePolynomialTest.language F T s):
    SquareSampleCompleteVertices.Valid F c w:=by
  change (SquareSampleCompleteVertices.Valid F (pairFst (pair c w)) (pairSnd (pair c w)) ∧_) at hq
  simp only [pairFst_pair,pairSnd_pair] at hq
  exact hq.1
attribute [local irreducible] ImplicitSourceComponentSampler.test SquareSampleCompletePolynomialTest.value
private theorem sampler_valid (c w:List Bool)
    (hq:pair c w∈FormulaSignSlotRadialJointStratumSampler.language):SquareSampleCompleteVertices.Valid F c w:=
  complete_valid (ImplicitSourceComponentSampler.test FormulaSignSlotRadialJointStratum.source
    FormulaSignSlotRadialJointStratumSampler.positive) 0 c w hq

/-- No valid-word or radius premise is required by the language specification. -/
theorem language_iff (c w:List Bool):pair c w∈language ↔
    ∃hw:SquareSampleCompleteVertices.Valid F c w,
      pair c w∈FormulaSignSlotRadialJointStratumSampler.language ∧
      ∀r∈Ioo 0 (env c w hw 3),r ∉ RealParameterRootBranches.bad (rows c w hw):=by
  constructor
  · intro H
    have hq:pair c w∈FormulaSignSlotRadialJointStratumSampler.language:=H.1
    let hw:=sampler_valid c w hq
    exact ⟨hw,(language_packet_iff c w hw).mp H⟩
  · rintro ⟨hw,H⟩
    exact (language_packet_iff c w hw).mpr H

end LeanCanny.Encoding.FormulaSignSlotRadialImplicitRootBranchCuts
