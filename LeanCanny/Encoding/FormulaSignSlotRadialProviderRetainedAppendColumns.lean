/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendMetadata
/-! # Exact physical-column clocks for the entire new retained tail -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedPhysicalIndex
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open FormulaSignSlotRadialProviderRecordPrefix (context)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem native_span (E : IntegralFramedBankQuery.Bank) (TT : IntegralMixedHeaderTablesBits.Tables)
    (c : List Bool) (b : ℕ)
    (h : (IntegralMixedFramedCriticalGuardBits.header TT (IntegralFramedPhysicalCriticalGuardTest.keyDatum E.key)
      IntegralFramedPhysicalCriticalGuardScan.stage (pair c (List.replicate b true))).context=1) :
    span E.parameters TT (pair (E.key c) (List.replicate b true))=
      block (E.parameters.ambient (pairFst (E.key c)))+1 := by
  have HH : IntegralMixedFramedCriticalGuardBits.header TT (IntegralFramedPhysicalCriticalGuardTest.keyDatum E.key)
      IntegralFramedPhysicalCriticalGuardScan.stage (pair c (List.replicate b true))=
        IntegralMixedCommandHeaderBits.lookup (TT.commands (pairFst (E.key c))) b := by
    simp only [IntegralMixedFramedCriticalGuardBits.header,IntegralFramedPhysicalCriticalGuardTest.keyDatum,
      IntegralFramedPhysicalCriticalGuardScan.stage,pairFst_pair,pairSnd_pair,List.length_replicate]
  unfold span
  simp only [pairFst_pair,pairSnd_pair,List.length_replicate]
  rw [←HH,h]
  exact ite_eq_left rfl

private theorem prefix_succ (PP : Parameters) (TT : IntegralMixedHeaderTablesBits.Tables) (key : List Bool) (b : ℕ) :
    prefixArity PP TT (pair key (List.replicate (b+1) true))=
      prefixArity PP TT (pair key (List.replicate b true))+span PP TT (pair key (List.replicate b true)) := by
  simp only [prefixArity,pairFst_pair,pairSnd_pair,List.length_replicate,Finset.sum_range_succ]

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderIntegerSource.source preparedRoot start parentCommands
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial

variable (old : List Bool) (hv : A old) (hd : depth old<dimension old)
  (e : ℕ) (he : e<endBirth (dimension old) (N old) old)

include hv hd he in
theorem span_after_begin (b : ℕ) (hb0 : N old+start old≤b) (hb1 : b<fullBirth old e) :
    span P T (pair ((B).key (context (preparedRoot old e))) (List.replicate b true))=2*dimension old+4 := by
  have H := native_span B T (context (preparedRoot old e)) b
    (active_after_begin old hv hd e he b hb0 hb1).2
  have HR := FormulaSignSlotRadialProviderRecordPrefix.key_root (preparedRoot old e)
  have HD := prepared_dimension old e
  have HE : block ((B).parameters.ambient (pairFst ((B).key (context (preparedRoot old e)))))+1=
      2*dimension old+4 := by
    change block ((P).ambient (pairFst ((B).key (context (preparedRoot old e)))))+1=_
    rw [HR,HD]
    unfold block
    omega
  exact H.trans HE

include hv hd he in
theorem prefix_arity_after_begin (b : ℕ) (hb0 : N old+start old≤b) (hb1 : b≤fullBirth old e) :
    prefixArity P T (pair ((B).key (context (preparedRoot old e))) (List.replicate b true))=
      arity (parentCommands old hv hd e he)+(2*dimension old+4)*(b-(N old+start old)) := by
  have HBase : prefixArity P T (pair ((B).key (context (preparedRoot old e)))
      (List.replicate (N old+start old) true))=arity (parentCommands old hv hd e he) := by
    have H := FormulaSignSlotRadialProviderRecordPrefix.prefix_arity_observation (preparedRoot old e)
      (start old) (prefix_fit old hv hd e he)
    rw [prepared_initial] at H
    exact H.trans (congrArg IntegralMixedFramedRunObservation.Data.arity (parent_observation old hv hd e he))
  have H (a : ℕ) (ha : N old+start old+a≤fullBirth old e) :
      prefixArity P T (pair ((B).key (context (preparedRoot old e)))
        (List.replicate (N old+start old+a) true))=
        arity (parentCommands old hv hd e he)+(2*dimension old+4)*a := by
    induction a with
    | zero => simpa only [Nat.add_zero,Nat.mul_zero] using HBase
    | succ a ih =>
      rw [show N old+start old+(a+1)=(N old+start old+a)+1 by omega,prefix_succ,
        ih (by omega),span_after_begin old hv hd e he _ (by omega) (by omega)]
      ring
  have HE : N old+start old+(b-(N old+start old))=b := Nat.add_sub_of_le hb0
  have HR := H (b-(N old+start old)) (by omega)
  rw [HE] at HR
  exact HR

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
