/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendMetadata
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendEndpointBoundary
/-! # Physical-column clocks after the proper MID and through the seed tail -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryScript
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

private theorem prefix_root_arity (E : IntegralFramedBankQuery.Bank) (TT : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents E.parameters E.plan E.data TT)
    (c root : List Bool) (hk : pairFst (E.key c)=root) (b : ℕ) :
    prefixArity E.parameters TT (pair (E.key c) (List.replicate b true))=
      arity (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction E.parameters E.plan root)
        (E.plan.rules root) b) := by
  subst root
  exact prefixArity_packet E.parameters E.plan E.data TT hr (E.key c) b

private theorem arity_scripts_heq {n m w z : ℕ}
    (cs : List (IntegralMixedFramedHistoryScript.Instruction n w))
    (ds : List (IntegralMixedFramedHistoryScript.Instruction m z))
    (hn : n=m) (hw : w=z) (he : HEq cs ds) : arity cs=arity ds := by
  cases hn
  cases hw
  cases eq_of_heq he
  rfl

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
  (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side
local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
  (FormulaSignSlotRadialProviderAtomic.ownBirth old)
local notation "oldCs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd
  (FormulaSignSlotRadialProviderAtomic.ownBirth old) (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old)

noncomputable def endpointArity := arity (R.result.commands.map (canonicalEndpointWrap old)++oldCs)

theorem midpoint_prefix_arity :
    prefixArity P T (pair ((B).key (context r)) (List.replicate (midpointBirth old hv hd left right R) true))=
      endpointArity old hv hd left right R := by
  have HP := (prepared_provider old R.leftSpec R.rightSpec side).trans
    (FormulaSignSlotRadialProviderRetainedAppend.prepared_provider old
      (FormulaSignSlotRadialProviderAtomic.ownBirth old)).symm
  have HE := arity_scripts_heq _ _ (FormulaSignSlotRadialProviderRecordPrefix.ambient r c HP)
    (FormulaSignSlotRadialProviderRecordPrefix.width r c HP)
    (midpoint_prefix_commands old hv hd left right R side)
  exact (prefix_root_arity B T FormulaSignSlotRadialProviderAtomic.bank_represents (context r) r
    (FormulaSignSlotRadialProviderRecordPrefix.key_root r) (midpointBirth old hv hd left right R)).trans HE

include hv hd in
theorem span_after_midpoint (b : ℕ) (hb0 : midpointBirth old hv hd left right R≤b) (hb1 : b<fullBirth old hv hd left right R side) :
    span P T (pair ((B).key (context r)) (List.replicate b true))=2*dimension old+4 := by
  have H := native_span B T (context r) b
    (active_after_midpoint old hv hd left right R side b hb0 hb1).2
  have HR := FormulaSignSlotRadialProviderRecordPrefix.key_root r
  have HD := prepared_dimension old R.leftSpec R.rightSpec side
  have HE : block ((B).parameters.ambient (pairFst ((B).key (context r))))+1=
      2*dimension old+4 := by
    change block ((P).ambient (pairFst ((B).key (context r))))+1=_
    rw [HR,HD]
    unfold block
    omega
  exact H.trans HE

include hv hd in
theorem prefix_arity_after_midpoint (b : ℕ) (hb0 : midpointBirth old hv hd left right R≤b) (hb1 : b≤fullBirth old hv hd left right R side) :
    prefixArity P T (pair ((B).key (context r)) (List.replicate b true))=
      prefixArity P T (pair ((B).key (context r)) (List.replicate (midpointBirth old hv hd left right R) true))+(2*dimension old+4)*(b-(midpointBirth old hv hd left right R)) := by
  have H (a : ℕ) (ha : midpointBirth old hv hd left right R+a≤fullBirth old hv hd left right R side) :
      prefixArity P T (pair ((B).key (context r))
        (List.replicate (midpointBirth old hv hd left right R+a) true))=
        prefixArity P T (pair ((B).key (context r)) (List.replicate (midpointBirth old hv hd left right R) true))+(2*dimension old+4)*a := by
    induction a with
    | zero => simp only [Nat.add_zero,Nat.mul_zero]
    | succ a ih =>
      rw [show midpointBirth old hv hd left right R+(a+1)=(midpointBirth old hv hd left right R+a)+1 by omega,prefix_succ,
        ih (by omega),span_after_midpoint old hv hd left right R side _ (by omega) (by omega)]
      ring
  have HE : midpointBirth old hv hd left right R+(b-(midpointBirth old hv hd left right R))=b := Nat.add_sub_of_le hb0
  have HR := H (b-(midpointBirth old hv hd left right R)) (by omega)
  rw [HE] at HR
  exact HR

theorem prefix_arity_after_midpoint_canonical (b : ℕ)
    (hb0 : midpointBirth old hv hd left right R≤b) (hb1 : b≤fullBirth old hv hd left right R side) :
    prefixArity P T (pair ((B).key (context r)) (List.replicate b true))=
      endpointArity old hv hd left right R+(2*dimension old+4)*(b-midpointBirth old hv hd left right R) := by
  rw [prefix_arity_after_midpoint old hv hd left right R side b hb0 hb1,
    midpoint_prefix_arity old hv hd left right R side]

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
