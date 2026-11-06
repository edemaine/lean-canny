/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordNative
public import LeanCanny.Encoding.IntegralMixedReservedCutActualVertex
/-! # The actual provider record factory realizes a typed last reserved cut

The certified plan is identified with its literal source-append view.
No interpreting hom, replacement word, or native evaluator is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderReservedCutRealization
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (family prefixLength)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem view_realizes (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (k : List Bool) (v : ℕ→ℝ)
    (hv : IntegralMixedIntegerRealization.Realizes ((family P D H).state k) v) :
    IntegralMixedIntegerRealization.Realizes (IntegralMixedFramedFamilyRunView.stateView P D H k) v :=hv

private def fullRun (a : Parameters) (e : IntegralMixedFramedHistoryFamilyBits.Plan a)
    (r : List Bool) (v : ℕ→ℝ) : Prop :=
  IntegralMixedIntegerRealization.Realizes
    (IntegralMixedFramedHistoryScript.run (IntegralMixedFramedHistoryFamilyBits.initial a e r) (e.rules r)
      (by have HR:=e.room r;omega)) v

private theorem fullRun_cast (a : Parameters) (e f : IntegralMixedFramedHistoryFamilyBits.Plan a)
    (he : e=f) (r : List Bool) (v : ℕ→ℝ) (hv : fullRun a e r v) : fullRun a f r v :=by
  cases he
  exact hv

private def cast_plan_data {a : Parameters} {e f : IntegralMixedFramedHistoryFamilyBits.Plan a}
    (he : e=f) (j : IntegralMixedFramedHistoryFamilyBits.Data a e) :
    IntegralMixedFramedHistoryFamilyBits.Data a f :=he ▸ j

private theorem view_cast (a : Parameters) (e f : IntegralMixedFramedHistoryFamilyBits.Plan a)
    (he : e=f) (j : IntegralMixedFramedHistoryFamilyBits.Data a e) (k : List Bool) (v : ℕ→ℝ)
    (hv : IntegralMixedIntegerRealization.Realizes (IntegralMixedFramedFamilyRunView.stateView a e j k) v) :
    IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedFamilyRunView.stateView a f (cast_plan_data he j) k) v :=by
  cases he
  exact hv

private theorem margin_for_source (a d b c lf ff kf : List Bool→ℕ) (r : List Bool) :
    let q:=IntegralMixedFramedNormalizationBits.planned
      (IntegralMixedSourceIntegerPrelude.parameters a d b c) lf ff kf
    IntegralMixedExceptionalBounds.auxiliaryCap (q.ambient r+1) (q.degree r)<2^q.width r :=
  (Nat.le_add_right _ _).trans_lt (Nat.lt_size_self _)

local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H
local notation "L"=>IntegralFramedBankQuery.Bank.nodes B
local notation "F"=>IntegralFramedBankQuery.Bank.factor B
local notation "C"=>IntegralFramedBankQuery.Bank.seed B
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds B
local notation "Input"=>IntegralFramedPhysicalSquare.input P D H L F C hs

theorem margin (r : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap ((P).ambient r+1) ((P).degree r)<2^(P).width r :=by
  have HM:=margin_for_source
    (FormulaSignSlotRadialProviderIntegerPlan.parameters.ambient∘FormulaSignSlotRadialProviderRecordPlan.providerContext)
    (FormulaSignSlotRadialProviderIntegerPlan.parameters.degree∘FormulaSignSlotRadialProviderRecordPlan.providerContext)
    FormulaSignSlotRadialProviderRecordPlan.degreeBound FormulaSignSlotRadialProviderRecordPlan.fullCount
    (fun _=>3) FormulaSignSlotRadialProviderRecordPlan.factor FormulaSignSlotRadialProviderRecordPlan.seed r
  simpa only [FormulaSignSlotRadialProviderRecordPlan.bank,FormulaSignSlotRadialProviderRecordPlan.certifiedParameters,
    FormulaSignSlotRadialProviderRecordPlan.parameters] using HM

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPlan.factor FormulaSignSlotRadialProviderRecordPlan.seed
  IntegralMixedFramedHistoryScript.run IntegralMixedHistory.reframe
  IntegralMixedIntegerRealization.Realizes IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus

private noncomputable def appendPlan : IntegralMixedFramedHistoryFamilyBits.Plan P :=
  IntegralMixedSourceIntegerRecordAppend.plan P
    (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial r)
    FormulaSignSlotRadialProviderRecordPlan.positive
    (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial_degree r)
    FormulaSignSlotRadialProviderRecordPlan.spatial_cap FormulaSignSlotRadialProviderRecordPlan.count
    FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.source_nonzero
    FormulaSignSlotRadialProviderRecordPlan.source_degree_cap FormulaSignSlotRadialProviderRecordPlan.room

private theorem appendPlan_eq : appendPlan=D :=rfl

private noncomputable def appendData : IntegralMixedFramedHistoryFamilyBits.Data P appendPlan :=
  cast_plan_data appendPlan_eq.symm H

private theorem raw_realizes (parent : List Bool) (codes : List (List Bool))
    (d : IntegralMixedCutRecordConstructor.Data ((P).ambient (pairFst parent))
      (FormulaSignSlotRadialProviderRecordPlan.count (pairFst parent)+codes.length))
    (tag : IntegralMixedCausalRecordBits.Tag) (choice degree : ℕ)
    (hdegree : degree≤IntegralMixedExceptionalBounds.auxiliaryCap ((P).ambient (pairFst parent)+1)
      ((P).degree (pairFst parent)))
    (htable : IntegralMixedCausalRecordPlanBits.records (pairFst parent)=WordList.encode
      (codes++[d.code tag choice degree]))
    (hprefix : prefixLength P parent=FormulaSignSlotRadialProviderRecordPlan.count (pairFst parent)+codes.length)
    (v : ℕ→ℝ) (hv : IntegralMixedIntegerRealization.Realizes ((G).state parent) v) :
    fullRun P appendPlan (pairFst parent) (IntegralFramedPaddedCutVertex.values v) :=by
  have HV0:=view_realizes P D H parent v hv
  have HV1:=view_cast P D appendPlan appendPlan_eq.symm H parent v HV0
  have HV : IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedFamilyRunView.stateView P appendPlan appendData parent) v:=by
    simpa only [appendData] using HV1
  have HD : degree≤IntegralMixedExceptionalBounds.auxiliaryCap ((P).ambient (pairFst parent)+1)
      (FormulaSignSlotRadialProviderRecordPlan.spatial (pairFst parent)).degree:=by
    rw [FormulaSignSlotRadialProviderRecordPlan.spatial_degree]
    exact hdegree
  unfold fullRun appendPlan
  exact IntegralMixedReservedCutActualVertex.run_realizes P
    (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial r)
    FormulaSignSlotRadialProviderRecordPlan.positive
    (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial_degree r)
    FormulaSignSlotRadialProviderRecordPlan.spatial_cap FormulaSignSlotRadialProviderRecordPlan.count
    FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.source_nonzero
    FormulaSignSlotRadialProviderRecordPlan.source_degree_cap FormulaSignSlotRadialProviderRecordPlan.room
    appendData parent codes d tag choice degree HD htable hprefix (margin (pairFst parent)) v HV

/-- The actual provider factory executes a genuine typed last cut, padding the
new quotient by zero and preserving every older quotient simultaneously. -/
theorem run_realizes (parent : List Bool) (codes : List (List Bool))
    (d : IntegralMixedCutRecordConstructor.Data ((P).ambient (pairFst parent))
      (FormulaSignSlotRadialProviderRecordPlan.count (pairFst parent)+codes.length))
    (tag : IntegralMixedCausalRecordBits.Tag) (choice degree : ℕ)
    (hdegree : degree≤IntegralMixedExceptionalBounds.auxiliaryCap ((P).ambient (pairFst parent)+1)
      ((P).degree (pairFst parent)))
    (htable : IntegralMixedCausalRecordPlanBits.records (pairFst parent)=WordList.encode
      (codes++[d.code tag choice degree]))
    (hprefix : prefixLength P parent=FormulaSignSlotRadialProviderRecordPlan.count (pairFst parent)+codes.length)
    (v : ℕ→ℝ) (hv : IntegralMixedIntegerRealization.Realizes ((G).state parent) v) :
    IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedHistoryScript.run (IntegralMixedFramedHistoryFamilyBits.initial P D (pairFst parent))
        ((D).rules (pairFst parent)) (by have HR:=(D).room (pairFst parent);omega))
      (IntegralFramedPaddedCutVertex.values v) :=by
  exact fullRun_cast P appendPlan D appendPlan_eq (pairFst parent)
    (IntegralFramedPaddedCutVertex.values v) (raw_realizes parent codes d tag choice degree hdegree htable hprefix v hv)

private theorem raw_length (parent : List Bool) (codes : List (List Bool)) (last : List Bool)
    (htable : IntegralMixedCausalRecordPlanBits.records (pairFst parent)=WordList.encode (codes++[last])) :
    (appendPlan.rules (pairFst parent)).length=
      FormulaSignSlotRadialProviderRecordPlan.count (pairFst parent)+codes.length+1 :=by
  unfold appendPlan
  exact IntegralMixedSourceIntegerLastCode.rules_length_last P
    (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial r)
    FormulaSignSlotRadialProviderRecordPlan.positive
    (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial_degree r)
    FormulaSignSlotRadialProviderRecordPlan.spatial_cap FormulaSignSlotRadialProviderRecordPlan.count
    FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.source_nonzero
    FormulaSignSlotRadialProviderRecordPlan.source_degree_cap FormulaSignSlotRadialProviderRecordPlan.room
    (pairFst parent) codes last htable

theorem rules_length (parent : List Bool) (codes : List (List Bool)) (last : List Bool)
    (htable : IntegralMixedCausalRecordPlanBits.records (pairFst parent)=WordList.encode (codes++[last])) :
    ((D).rules (pairFst parent)).length=
      FormulaSignSlotRadialProviderRecordPlan.count (pairFst parent)+codes.length+1 :=by
  have HE:=congrArg (fun e : IntegralMixedFramedHistoryFamilyBits.Plan P=>(e.rules (pairFst parent)).length) appendPlan_eq
  exact HE.symm.trans (raw_length parent codes last htable)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderReservedCutRealization
