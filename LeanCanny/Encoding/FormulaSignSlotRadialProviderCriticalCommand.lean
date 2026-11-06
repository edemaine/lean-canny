/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalPrefixes
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalCommand
/-! # The prepared provider probe is its literal appended critical command -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalCommand
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalQuery (root lastCode)
open FormulaSignSlotRadialProviderCriticalPrefixes (birth)
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
 FormulaSignSlotRadialProviderRecordPlan.plan FormulaSignSlotRadialProviderRecordPlan.source

 theorem command (q : List Bool)
    (hp : 0<IntegralMixedCausalRecordPlanBits.count (root q))
    (hc : IntegralMixedUnitRecordCode.critical (lastCode q)=true) :
    (IntegralMixedFramedRootPullback.instructionAt FormulaSignSlotRadialProviderRecordPlan.certifiedParameters FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
      (root q) (birth false q)).command=
      .critical (IntegralMixedCausalUnitRecordBits.physical
        (FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.ambient (root q)) (birth false q) (lastCode q)) :=by
  have hb : IntegralMixedCausalRecordPlanBits.count (root q)-1<
      IntegralMixedCausalRecordPlanBits.count (root q):=by omega
  have HE:=IntegralMixedPhysicalCriticalCommand.instruction_critical FormulaSignSlotRadialProviderRecordPlan.parameters
    (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial r) FormulaSignSlotRadialProviderRecordPlan.positive (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial_degree r) FormulaSignSlotRadialProviderRecordPlan.spatial_cap
    FormulaSignSlotRadialProviderRecordPlan.count FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.source_nonzero FormulaSignSlotRadialProviderRecordPlan.source_degree_cap FormulaSignSlotRadialProviderRecordPlan.room
    (root q) _ hb hc
  have Hplan : IntegralMixedSourceIntegerRecordAppend.plan FormulaSignSlotRadialProviderRecordPlan.parameters
      (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial r) FormulaSignSlotRadialProviderRecordPlan.positive
      (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial_degree r) FormulaSignSlotRadialProviderRecordPlan.spatial_cap
      FormulaSignSlotRadialProviderRecordPlan.count FormulaSignSlotRadialProviderRecordPlan.source
      FormulaSignSlotRadialProviderRecordPlan.source_nonzero FormulaSignSlotRadialProviderRecordPlan.source_degree_cap
      FormulaSignSlotRadialProviderRecordPlan.room=FormulaSignSlotRadialProviderRecordPlan.plan := by
    unfold FormulaSignSlotRadialProviderRecordPlan.plan
    rfl
  rw [Hplan] at HE
  have HB : FormulaSignSlotRadialProviderRecordPlan.count (root q)+(IntegralMixedCausalRecordPlanBits.count (root q)-1)=birth false q:=by
    simp only [FormulaSignSlotRadialProviderCriticalPrefixes.birth,FormulaSignSlotRadialProviderRecordPlan.fullCount,Bool.false_eq_true,ite_false]
    omega
  rw [HB] at HE
  change (IntegralMixedFramedRootPullback.instructionAt FormulaSignSlotRadialProviderRecordPlan.parameters
    FormulaSignSlotRadialProviderRecordPlan.plan (root q) (birth false q)).command=
      .critical (IntegralMixedCausalUnitRecordBits.physical
        (FormulaSignSlotRadialProviderRecordPlan.parameters.ambient (root q)) (birth false q) (lastCode q))
  simpa only [IntegralMixedCausalRecordPlanBits.code,lastCode] using HE

theorem command_data (q : List Bool)
    (hp : 0<IntegralMixedCausalRecordPlanBits.count (root q))
    (d : IntegralMixedCriticalRecordConstructor.Data
      (FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.ambient (root q)) (birth false q)) (hd : lastCode q=d.code) :
    (IntegralMixedFramedRootPullback.instructionAt FormulaSignSlotRadialProviderRecordPlan.certifiedParameters FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
      (root q) (birth false q)).command=.critical d.rule :=by
  have hc : IntegralMixedUnitRecordCode.critical (lastCode q)=true:=by
    simp only [hd,IntegralMixedUnitRecordCode.critical,IntegralMixedCriticalRecordConstructor.field_0,
      List.getElem?_cons_zero,Option.getD_some]
  simpa only [hd,IntegralMixedCriticalRecordConstructor.rule_decode] using command q hp hc

theorem packet_command (q : List Bool)
    (d : IntegralMixedCriticalRecordConstructor.Data
      (FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.ambient (root q)) (birth false q))
    (ctx w : List Bool) (a b : ℕ) (he : d.coordinate.val=d.objective.val)
    (hq : q=IntegralMixedPhysicalCriticalQuery.packet ctx d.code w a b) :
    (IntegralMixedFramedRootPullback.instructionAt FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
      FormulaSignSlotRadialProviderRecordPlan.certifiedPlan (root q) (birth false q)).command=.critical d.rule :=by
  have HD : lastCode q=d.code :=(congrArg lastCode hq).trans
    ((IntegralMixedPhysicalCriticalQuery.lastCode_packet ctx d.code w a b).trans
      (IntegralMixedPhysicalCriticalQuery.normalize_data d he))
  have HP:= (IntegralMixedPhysicalCriticalQuery.critical_packet ctx d.code w a b).1
  have HC:=congrArg (fun z=>0<IntegralMixedCausalRecordPlanBits.count (root z)) hq
  exact command_data q (HC.mpr HP) d HD

theorem point_command (q : List Bool)
    {F : IntegralMixedFrozenFrame.Frame (FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.ambient (root q))}
    (HA : IntegralMixedFrozenFrame.AtomicRows F (birth false q))
    (h : Fin (FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.ambient (root q)+1)) (hh : h∉F.frozen)
    (ctx w : List Bool) (a b : ℕ)
    (hq : q=IntegralMixedPhysicalCriticalQuery.packet ctx (HA.pointData h h hh hh).code w a b) :
    (IntegralMixedFramedRootPullback.instructionAt FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
      FormulaSignSlotRadialProviderRecordPlan.certifiedPlan (root q) (birth false q)).command=
      .critical (HA.pointData h h hh hh).rule :=
  packet_command q (HA.pointData h h hh hh) ctx w a b rfl hq


end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalCommand
