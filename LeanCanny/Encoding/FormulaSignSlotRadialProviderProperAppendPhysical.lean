/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendColumns
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendSampledLevel
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPoweredReadback
/-! # Native geometric block readback on the actual proper own word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedPhysicalIndex
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem proper_candidate_from_joint (E : IntegralFramedBankQuery.Bank) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input E) c w)
    (u : ℕ→ℝ) (HJ : ∀i : Fin (IntegralFramedPhysicalSquare.count E.parameters E.plan (E.key c)),
      IntegralFramedPhysicalSquare.joint E.parameters E.plan E.data E.nodes E.factor E.seed E.bounds
        E.key E.positive c w hw i=u i.val)
    (i : Fin ((IntegralFramedPhysicalBankTerm.input E).count c)) :
    (SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input E) c w hw).val i=u i.val := HJ i

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
  (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side
local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
  (FormulaSignSlotRadialProviderAtomic.ownBirth old)
local notation "D" => FormulaSignSlotRadialProviderAtomic.dimension old

private theorem provider_canonical : FormulaSignSlotRadialProviderRecordPlan.providerContext r=
    FormulaSignSlotRadialProviderRecordPlan.providerContext c := (prepared_provider old R.leftSpec R.rightSpec side).trans
  (FormulaSignSlotRadialProviderRetainedAppend.prepared_provider old (FormulaSignSlotRadialProviderAtomic.ownBirth old)).symm

private theorem count_canonical : IntegralMixedCausalRecordPlanBits.count r=IntegralMixedCausalRecordPlanBits.count c :=
  (prepared_count old hv hd R.leftSpec R.rightSpec side (endpoints_good old hv hd left right R)).trans
    (FormulaSignSlotRadialProviderRetainedAppend.prepared_count old hv hd
      (FormulaSignSlotRadialProviderAtomic.ownBirth old) (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old)).symm

theorem native_dimension : (B).parameters.ambient (pairFst ((B).key (C r)))=(P).ambient c := by
  change (P).ambient (pairFst ((B).key (C r)))=_
  rw [FormulaSignSlotRadialProviderRecordPrefix.key_root]
  exact FormulaSignSlotRadialProviderRecordPrefix.ambient r c (provider_canonical old hv hd left right R side)

noncomputable def nativePoint (p : Fin ((P).ambient c+1)→ℝ) :
    Fin ((B).parameters.ambient (pairFst ((B).key (C r)))+1)→ℝ := fun i=>
  p (Fin.cast (congrArg (·+1) (native_dimension old hv hd left right R side)) i)

private theorem physical_power (b : ℕ) :
    IntegralMixedFramedCriticalGuardBits.physicalPower (B).parameters (B).key (fun _=>b) (C r)=
      UniformIntegralPowerSchedule.physical ((P).cap c+1) (2^(P).width c) b := by
  unfold IntegralMixedFramedCriticalGuardBits.physicalPower
  rw [FormulaSignSlotRadialProviderRecordPrefix.key_root]
  change UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b=_
  rw [
    FormulaSignSlotRadialProviderRecordPrefix.cap r c (provider_canonical old hv hd left right R side)
      (count_canonical old hv hd left right R side),
    FormulaSignSlotRadialProviderRecordPrefix.width r c (provider_canonical old hv hd left right R side)]

private theorem native_column_lt (b : ℕ)
    (hb : FormulaSignSlotRadialProviderAtomic.Active (C r) b)
    (i : Fin ((B).parameters.ambient (pairFst ((B).key (C r)))+1)) :
    prefixArity (B).parameters T (LeanCanny.pair ((B).key (C r)) (List.replicate b true))+i.val<
      FormulaSignSlotRadialProviderAtomic.input.count (C r) := by
  have H := IntegralMixedFramedPointEqualityBits.column_lt (B).parameters T (B).key (fun _=>i.val)
    (fun _=>b) (C r) (IntegralFramedPhysicalCompanionPoint.active_direct B T _ _ hb) i.isLt
  have HC := IntegralFramedPhysicalCompanionPoint.count_eq B T FormulaSignSlotRadialProviderAtomic.bank_represents (C r) []
  have HE : IntegralMixedFramedCriticalGuardBits.count (B).parameters T (B).key (C r)=
      FormulaSignSlotRadialProviderAtomic.input.count (C r) := by
    simpa only [IntegralMixedFramedCriticalGuardBits.count,IntegralMixedFramedCriticalGuardBits.packet,
      IntegralFramedPhysicalCriticalGuardTest.keyDatum,Function.comp_apply,pairFst_pair] using HC
  exact H.trans_eq HE

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentState

private theorem geometric_of_powered {pMID pChild : Fin ((P).ambient c+1)→ℝ}
    (S : SampledLevel old hv hd left right R side pMID pChild)
    (b : ℕ) (hb0 : midpointBirth old hv hd left right R≤b) (hb1 : b<finishBirth old hv hd left right R side)
    (p : Fin ((P).ambient c+1)→ℝ)
    (HP : ∀j : Fin ((P).ambient c+1),
      S.receipt.tuple (endpointArity old hv hd left right R+(2*D+4)*(b-midpointBirth old hv hd left right R)+j.val)^
        UniformIntegralPowerSchedule.physical ((P).cap c+1) (2^(P).width c) b=p j) :
    FormulaSignSlotRadialProviderAtomic.geometricPoint (C r) S.receipt.word S.receipt.valid b=
      nativePoint old hv hd left right R side p := by
  have HA := active_after_midpoint old hv hd left right R side b hb0
    (hb1.trans_le (finish_le_full old hv hd left right R side))
  funext i
  let j := Fin.cast (congrArg (·+1) (native_dimension old hv hd left right R side)) i
  have HCol := native_column_lt old hv hd left right R side b HA i
  have HValue := proper_candidate_from_joint B (C r) S.receipt.word S.receipt.valid S.receipt.tuple S.receipt.joint ⟨_,HCol⟩
  have HE : prefixArity (B).parameters T (LeanCanny.pair ((B).key (C r)) (List.replicate b true))+i.val=
      endpointArity old hv hd left right R+(2*D+4)*(b-midpointBirth old hv hd left right R)+j.val := by
    change prefixArity P T (LeanCanny.pair ((B).key (C r)) (List.replicate b true))+i.val=_
    rw [prefix_arity_after_midpoint_canonical old hv hd left right R side b hb0
      (hb1.le.trans (finish_le_full old hv hd left right R side))]
    simp only [j,Fin.val_cast]
  unfold FormulaSignSlotRadialProviderAtomic.geometricPoint IntegralFramedPhysicalCompanionPoint.geometricPoint
    IntegralFramedPhysicalCompanionPoint.block
  rw [dite_eq_left HCol,HValue,physical_power]
  change S.receipt.tuple (prefixArity (B).parameters T
    (LeanCanny.pair ((B).key (C r)) (List.replicate b true))+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap c+1) (2^(P).width c) b=p j
  rw [HE]
  exact HP j

theorem SampledLevel.local_geometric_point {pMID pChild : Fin ((P).ambient c+1)→ℝ}
    (S : SampledLevel old hv hd left right R side pMID pChild)
    (b : ℕ) (hb0 : midpointBirth old hv hd left right R≤b) (hb1 : b<finishBirth old hv hd left right R side) :
    FormulaSignSlotRadialProviderAtomic.geometricPoint (C r) S.receipt.word S.receipt.valid b=
      nativePoint old hv hd left right R side
        (if b<midpointBirth old hv hd left right R+1+(D-FormulaSignSlotRadialProviderAtomic.depth old)
          then pMID else pChild) := by
  apply geometric_of_powered old hv hd left right R side S b hb0 hb1
  intro j
  simpa only [ite_apply] using S.local_powered old hv hd left right R side b hb0 hb1 j

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
