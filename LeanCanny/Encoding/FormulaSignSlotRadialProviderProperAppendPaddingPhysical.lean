/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendScalarReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPoweredReadback
/-! # Every own-word padding block is the same actual new-root padding point -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem padding_joint_value (B :IntegralFramedBankQuery.Bank) (c w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (u :ℕ→ℝ) (HJ :∀i :Fin (IntegralFramedPhysicalSquare.count B.parameters B.plan (B.key c)),
      IntegralFramedPhysicalSquare.joint B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
        B.key B.positive c w hw i=u i.val)
    (i :Fin ((IntegralFramedPhysicalBankTerm.input B).count c)) :
    (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hw).val i=u i.val:=HJ i

local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "T"=>FormulaSignSlotRadialProviderRecordPlan.tables
local notation "C"=>FormulaSignSlotRadialProviderRecordPrefix.context

private theorem padding_bank_parameters :(B).parameters=P:=rfl

theorem padding_native_dimension (root :List Bool) :
    (B).parameters.ambient (pairFst ((B).key (C root)))=(P).ambient root:=
  congrArg (B).parameters.ambient (FormulaSignSlotRadialProviderRecordPrefix.key_root root)

noncomputable def nativePaddingPoint (root :List Bool) (p0 :Fin ((P).ambient root+1)→ℝ) :
    Fin ((B).parameters.ambient (pairFst ((B).key (C root)))+1)→ℝ:=
  fun i=>p0 (Fin.cast (congrArg (·+1) (padding_native_dimension root)) i)

private theorem padding_physical_power (root :List Bool) (b :ℕ) :
    IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters (B).key (fun _=>b) (C root)=
      UniformIntegralPowerSchedule.physical ((P).cap root+1) (2^(P).width root) b:=by
  unfold IntegralMixedFramedCriticalGuardBits.physicalPower
  rw [FormulaSignSlotRadialProviderRecordPrefix.key_root]
  rfl

private theorem padding_column_lt (root :List Bool) (b :ℕ)
    (hb :FormulaSignSlotRadialProviderAtomic.Active (C root) b)
    (i :Fin ((B).parameters.ambient (pairFst ((B).key (C root)))+1)) :
    prefixArity (B).parameters T (pair ((B).key (C root)) (List.replicate b true))+i.val<
      FormulaSignSlotRadialProviderAtomic.input.count (C root):=by
  have H:=IntegralMixedFramedPointEqualityBits.column_lt (B).parameters T (B).key (fun _=>i.val)
    (fun _=>b) (C root) (IntegralFramedPhysicalCompanionPoint.active_direct B T _ _ hb) i.isLt
  have HC:=IntegralFramedPhysicalCompanionPoint.count_eq B T
    FormulaSignSlotRadialProviderAtomic.bank_represents (C root) []
  have HE:IntegralMixedFramedCriticalGuardBits.count (B).parameters T (B).key (C root)=
      FormulaSignSlotRadialProviderAtomic.input.count (C root):=by
    simpa only [IntegralMixedFramedCriticalGuardBits.count,IntegralMixedFramedCriticalGuardBits.packet,
      IntegralFramedPhysicalCriticalGuardTest.keyDatum,Function.comp_apply,pairFst_pair] using HC
  exact H.trans_eq HE

variable (old :List Bool) (hv :FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd :FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
  (left right :ParentEndpoint old hv hd) (R :CanonicalPair old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot old R.leftSpec R.rightSpec side
local notation "c"=>FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
  (FormulaSignSlotRadialProviderAtomic.ownBirth old)
local notation "mid"=>midpointBirth old hv hd left right R
local notation "finish"=>finishBirth old hv hd left right R side
local notation "full"=>fullBirth old hv hd left right R side
local notation "Dold"=>FormulaSignSlotRadialProviderAtomic.dimension old
local notation "K"=>Dold-FormulaSignSlotRadialProviderAtomic.depth old
local notation "program"=>compiledProgram old hv hd left right R side
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot preparedRoot
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentValues
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.depth

theorem prefix_arity_after_finish (b :ℕ) (hb0 :finish≤b) (hb1 :b≤full) :
    prefixArity P T (pair ((B).key (C r)) (List.replicate b true))=
      arity program+(2*Dold+4)*(b-finish):=by
  have HF:=finish_eq old hv hd left right R side
  have HM:=midpoint_lt_finish old hv hd left right R side
  have HP:=prefix_arity_after_midpoint_canonical old hv hd left right R side b (by omega) hb1
  have HA:arity program=(canonicalObservation old hv hd left right R side).arity:=by
    simpa only [compiledObservation,IntegralMixedFramedRunObservation.ofCommands] using
      tuple_arity old hv hd left right R side
  have HBase:arity program=endpointArity old hv hd left right R+(2*Dold+4)*(finish-mid):=by
    have HArity:=HA.trans (canonical_local_arity old hv hd left right R side)
    have HClock:finish-mid=2+2*K:=by omega
    rw [HClock]
    exact HArity
  have HSub:b-mid=(finish-mid)+(b-finish):=by omega
  rw [HP,HBase,HSub,Nat.mul_add]
  omega

theorem SampledLevel.padding_geometric_point
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (S :SampledLevel old hv hd left right R side pMID pChild)
    (b :ℕ) (hb0 :finish≤b) (hb1 :b<full) :
    FormulaSignSlotRadialProviderAtomic.geometricPoint (C r) S.receipt.word S.receipt.valid b=
      nativePaddingPoint r S.paddingPoint:=by
  have HA:=(seed_metadata_after_finish old hv hd left right R side b hb0 hb1).1
  have HL:=compiled_program_length old hv hd left right R side
  have HF:=padded_program_length old hv hd left right R side
  have HD:(P).ambient r=Dold:=prepared_dimension old R.leftSpec R.rightSpec side
  let js:=IntegralMixedCanonicalPadding.paddingSelections ((P).ambient r) (tailCount old hv hd left right R side)
  let j:Fin js.length:=⟨js.length-1-(b-finish),by
    change full=(program).length+js.length at HF
    omega⟩
  have HJ:js.length-1-j.val=b-finish:=by
    dsimp only [j]
    change full=(program).length+js.length at HF
    omega
  funext i
  let k:=Fin.cast (congrArg (·+1) (padding_native_dimension r)) i
  have HB:=S.receipt.padding_blocks j k
  change S.receipt.tuple (arity program+(2*(P).ambient r+4)*(js.length-1-j.val)+k.val)^
      UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r)
        ((program).length+(js.length-1-j.val))=S.paddingPoint k at HB
  rw [HJ,HL,Nat.add_sub_of_le hb0] at HB
  have HCol:=padding_column_lt r b HA i
  have HValue:=padding_joint_value B (C r) S.receipt.word S.receipt.valid S.receipt.tuple S.receipt.joint ⟨_,HCol⟩
  have HColumn:prefixArity (B).parameters T (pair ((B).key (C r)) (List.replicate b true))+i.val=
      arity program+(2*(P).ambient r+4)*(b-finish)+k.val:=by
    have HP:prefixArity (B).parameters T (pair ((B).key (C r)) (List.replicate b true))=
        arity program+(2*Dold+4)*(b-finish):=
      (congrArg (fun A=>prefixArity A T (pair ((B).key (C r)) (List.replicate b true)))
        padding_bank_parameters).trans (prefix_arity_after_finish old hv hd left right R side b hb0 hb1.le)
    simp only [HP,HD,k,Fin.val_cast]
  unfold FormulaSignSlotRadialProviderAtomic.geometricPoint IntegralFramedPhysicalCompanionPoint.geometricPoint
    IntegralFramedPhysicalCompanionPoint.block
  rw [dite_eq_left HCol,HValue,padding_physical_power]
  change S.receipt.tuple (prefixArity (B).parameters T
    (pair ((B).key (C r)) (List.replicate b true))+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b=S.paddingPoint k
  rw [HColumn]
  exact HB

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
