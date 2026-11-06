/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialGuardedFeasibility
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitRootBranchCuts
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitHeadReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitValueMeaning
/-! # Concrete PSPACE checking of every guard on one complete joint word -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialGuardedFeasibilityNative
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation Polynomial Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input
local notation "env" => FormulaSignSlotRadialImplicitSourceTest.env

private def NoRoot (p:ℝ[X]) (b:ℝ):Prop:=∀r,p.eval r=0 → r ∉ Ioo 0 b
private theorem cuts_iff (u:List Bool) (a:Fin (FormulaSignSlotCenteredRadialGraph.d u)→ℝ) (b:ℝ):
    (∀r∈Ioo 0 b,r ∉ FormulaSignSlotRadialBranchCuts.cuts u a)↔
      (∀j,NoRoot (FormulaSignSlotRadialParameterEliminant.coordinate u a j).leadingCoeff b) ∧
      (∀r∈Ioo 0 b,r ∉ RealParameterRootBranches.bad (FormulaSignSlotRadialParameterEliminant.coordinate u a)) ∧
      NoRoot (FormulaSignSlotRadialValueCertificate.polynomial u a).trailingCoeff b ∧
      NoRoot (FormulaSignSlotRadialParameterEliminant.coordinate u a (FormulaSignSlotCenteredRadialGraph.marginIndex u)).trailingCoeff b:=by
  constructor
  · intro H
    refine ⟨?_,?_,?_,?_⟩
    · intro j r hz hr
      exact (FormulaSignSlotRadialBranchCuts.conditions u a r (H r hr)).1 ⟨j,hz⟩
    · intro r hr
      exact (FormulaSignSlotRadialBranchCuts.conditions u a r (H r hr)).2.1
    · intro r hz hr
      exact (FormulaSignSlotRadialBranchCuts.conditions u a r (H r hr)).2.2.1 hz
    · intro r hz hr
      exact (FormulaSignSlotRadialBranchCuts.conditions u a r (H r hr)).2.2.2 hz
  · rintro ⟨HL,HB,HV,HM⟩ r hr hbad
    unfold FormulaSignSlotRadialBranchCuts.cuts at hbad
    rcases hbad with ((hL|hB)|hV)|hM
    · obtain ⟨j,hz⟩:=hL
      exact HL j r hz hr
    · exact HB r hr hB
    · exact HV r hV hr
    · exact HM r hM hr

attribute [local irreducible] FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotRadialParameterEliminant.coordinate
  FormulaSignSlotRadialValueCertificate.polynomial

private theorem rows_actual (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w):
    FormulaSignSlotRadialImplicitRootBranchCuts.rows c w hw=FormulaSignSlotRadialImplicitHeadReadback.coordinate c w hw:=by
  funext j
  unfold FormulaSignSlotRadialImplicitRootBranchCuts.rows FormulaSignSlotRadialImplicitHeadReadback.coordinate
  apply congrArg (FormulaSignSlotRadialParameterEliminant.coordinate
    (FormulaSignSlotRadialImplicitHeadReadback.root c) (FormulaSignSlotRadialImplicitHeadReadback.center c w hw))
  exact Fin.ext rfl

private theorem root_holds_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (hb:0<env c w hw 3):
    FormulaSignSlotRadialImplicitRootBranchCuts.Holds (pair c w)↔
      (∀j,NoRoot (FormulaSignSlotRadialImplicitHeadReadback.coordinate c w hw j).leadingCoeff (env c w hw 3)) ∧
      (∀r∈Ioo 0 (env c w hw 3),r ∉ RealParameterRootBranches.bad (FormulaSignSlotRadialImplicitHeadReadback.coordinate c w hw)):=by
  have HB:=FormulaSignSlotRadialImplicitRootBranchCuts.holds_packet_iff c w hw hb
  rw [rows_actual] at HB
  constructor
  · intro H
    refine ⟨?_,HB.mp H⟩
    intro j
    have HC:FormulaSignSlotRadialImplicitRootBranchCuts.count (pair c w)=
        FormulaSignSlotCenteredRadialGraph.N (FormulaSignSlotRadialImplicitHeadReadback.root c)+
          FormulaSignSlotCenteredRadialGraph.d (FormulaSignSlotRadialImplicitHeadReadback.root c)+1:=by
      simp only [FormulaSignSlotRadialImplicitRootBranchCuts.count,pairFst_pair]
      rfl
    have HL:FormulaSignSlotRadialImplicitHeadSelection.Leading (pair (pair c w) (BinaryNatCode.encode j.val)):=
      (H j.val (j.isLt.trans_eq HC.symm)).1
    exact (FormulaSignSlotRadialImplicitHeadReadback.leading_packet_iff c w hw j hb).mp HL
  · intro H
    exact HB.mpr H.2

private theorem center_eq (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w):
    FormulaSignSlotRadialJointGeometry.center (FormulaSignSlotRadialImplicitGridTest.header c) (env c w hw)=
      FormulaSignSlotRadialImplicitHeadReadback.center c w hw:=by
  funext i
  unfold FormulaSignSlotRadialJointGeometry.center FormulaSignSlotRadialImplicitHeadReadback.center FormulaSignSlotRadialJointLayout.column
  exact Nat.add_zero (4*i.val) ▸ rfl

private theorem point_cuts_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w) (hb:0<env c w hw 3):
    FormulaSignSlotRadialGuardedFeasibility.PointCuts (FormulaSignSlotRadialImplicitGridTest.header c) (env c w hw)↔
      FormulaSignSlotRadialImplicitRootBranchCuts.Holds (pair c w) ∧
      NoRoot (FormulaSignSlotRadialValueCertificate.polynomial (FormulaSignSlotRadialImplicitHeadReadback.root c)
        (FormulaSignSlotRadialImplicitHeadReadback.center c w hw)).trailingCoeff (env c w hw 3) ∧
      NoRoot (FormulaSignSlotRadialImplicitHeadReadback.coordinate c w hw
        (FormulaSignSlotCenteredRadialGraph.marginIndex (FormulaSignSlotRadialImplicitHeadReadback.root c))).trailingCoeff (env c w hw 3):=by
  unfold FormulaSignSlotRadialGuardedFeasibility.PointCuts
  rw [center_eq, cuts_iff]
  have HR:=root_holds_iff c w hw hb
  rw [HR]
  simp only [FormulaSignSlotRadialImplicitHeadReadback.coordinate,FormulaSignSlotRadialImplicitHeadReadback.root,
    FormulaSignSlotRadialJointLayout.boundVariable,and_assoc]

private theorem value_iff (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w):
    pair c w∈FormulaSignSlotRadialImplicitValueInterval.language↔
      pair c w∈FormulaSignSlotRadialJointStratumSampler.language ∧
      NoRoot (FormulaSignSlotRadialValueCertificate.polynomial (FormulaSignSlotRadialImplicitHeadReadback.root c)
        (FormulaSignSlotRadialImplicitHeadReadback.center c w hw)).trailingCoeff (env c w hw 3):=
  FormulaSignSlotRadialImplicitValueMeaning.actual_language_packet_iff c w hw

noncomputable def Checks (p:List Bool):Prop:=p∈FormulaSignSlotRadialImplicitGridSelection.language ∧
  p∈FormulaSignSlotRadialImplicitRootBranchCuts.language ∧
  p∈FormulaSignSlotRadialImplicitValueInterval.language ∧p∈FormulaSignSlotRadialImplicitHeadReadback.language

theorem checks_decider:SpaceDecider {p|Checks p}:=by
  have EG:=FormulaSignSlotRadialImplicitGridSelection.decider.flagEvaluator
  have ER:=FormulaSignSlotRadialImplicitRootBranchCuts.decider.flagEvaluator
  have EV:=FormulaSignSlotRadialImplicitValueInterval.decider.flagEvaluator
  have EM:=FormulaSignSlotRadialImplicitHeadReadback.decider.flagEvaluator
  apply (EG.andFlags (ER.andFlags (EV.andFlags EM))).decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro p
  simp only [Checks,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

private theorem filter_packet (I:SquareSampleInput.Inputs) (P:List Bool→Prop) (c w:List Bool):
    (pair c w∈({p|SquareSampleCompleteVertices.Valid I (pairFst p) (pairSnd p) ∧P p}:Language))↔
      SquareSampleCompleteVertices.Valid I c w ∧P (pair c w):=by
  simp only [Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair]
private theorem grid_packet (c w:List Bool):pair c w∈FormulaSignSlotRadialImplicitGridSelection.language↔
    SquareSampleCompleteVertices.Valid F c w ∧FormulaSignSlotRadialImplicitGridSelection.Holds (pair c w):=
  filter_packet F FormulaSignSlotRadialImplicitGridSelection.Holds c w
private theorem grid_env_eq (c w:List Bool) (hw:SquareSampleCompleteVertices.Valid F c w):
    FormulaSignSlotRadialImplicitGridTest.env c w hw=env c w hw:=rfl
private theorem own_good_iff (c w:List Bool):FormulaSignSlotRadialGuardedFeasibility.OwnGood c w↔
    pair c w∈FormulaSignSlotRadialJointStratumSampler.language ∧
      ∃hw:SquareSampleCompleteVertices.Valid F c w,
        FormulaSignSlotRadialImplicitGridSelection.Holds (pair c w) ∧
        FormulaSignSlotRadialGuardedFeasibility.PointCuts (FormulaSignSlotRadialImplicitGridTest.header c) (env c w hw):=by
  unfold FormulaSignSlotRadialGuardedFeasibility.OwnGood
  simp_rw [grid_env_eq]

attribute [local irreducible] FormulaSignSlotRadialImplicitGridSelection.language
  FormulaSignSlotRadialImplicitGridTest.env FormulaSignSlotRadialImplicitSourceTest.env
  ImplicitSourceGramGrid.input FormulaSignSlotRadialJointStratum.source SquareSampleCompleteVertices.Valid

private theorem checks_packet_iff (c w:List Bool):Checks (pair c w)↔FormulaSignSlotRadialGuardedFeasibility.OwnGood c w:=by
  constructor
  · rintro ⟨HG,HR,HV,HM⟩
    obtain ⟨hw,hGrid⟩:=(grid_packet c w).mp HG
    have hq:pair c w∈FormulaSignSlotRadialJointStratumSampler.language:=HR.1
    have hb:=FormulaSignSlotRadialImplicitRootBranchCuts.bound_positive c w hw hq
    refine (own_good_iff c w).mpr ⟨hq,hw,hGrid,(point_cuts_iff c w hw hb).mpr ⟨HR.2,?_,?_⟩⟩
    · exact ((value_iff c w hw).mp HV).2
    · exact (FormulaSignSlotRadialImplicitHeadReadback.language_packet_iff c w hw hb).mp HM
  · intro H
    obtain ⟨hq,hw,HG,HC⟩:=(own_good_iff c w).mp H
    have hb:=FormulaSignSlotRadialImplicitRootBranchCuts.bound_positive c w hw hq
    obtain ⟨HR,HV,HM⟩:=(point_cuts_iff c w hw hb).mp HC
    exact ⟨(grid_packet c w).mpr ⟨hw,HG⟩,⟨hq,HR⟩,(value_iff c w hw).mpr ⟨hq,HV⟩,
      (FormulaSignSlotRadialImplicitHeadReadback.language_packet_iff c w hw hb).mpr HM⟩

def normalize (p:List Bool):=pair (pairFst p) (pairSnd p)
theorem normalize_FP:normalize∈FP:=mem_FP_pair pairFst_mem_FP pairSnd_mem_FP

/-- Every constituent reader is applied to this one unchanged sampler query. -/
theorem word_decider:SpaceDecider FormulaSignSlotRadialGuardedFeasibility.wordLanguage:=by
  have D:=checks_decider.precompose normalize normalize_FP
  apply D.congr
  ext p
  exact checks_packet_iff (pairFst p) (pairSnd p)

theorem decider:SpaceDecider FormulaSignSlotRadialGuardedFeasibility.language:=
  FormulaSignSlotRadialProviderGuardedJointWitness.decider
    FormulaSignSlotRadialGuardedFeasibility.wordLanguage word_decider

theorem mem_PSPACE:FormulaSignSlotRadialGuardedFeasibility.language∈PSPACE:=decider.mem_PSPACE

theorem feasible_mem_PSPACE:({H|FormulaSignSlotRadialJointFeasibility.Feasible H}:Language)∈PSPACE:=by
  have HE:FormulaSignSlotRadialGuardedFeasibility.language={H|FormulaSignSlotRadialJointFeasibility.Feasible H}:=by
    ext H
    exact FormulaSignSlotRadialGuardedFeasibility.language_iff_feasible H
  exact HE ▸ mem_PSPACE

end LeanCanny.Connectivity.FormulaSignSlotRadialGuardedFeasibilityNative
