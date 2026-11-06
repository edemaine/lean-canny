/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPhysical
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPhaseValues
/-! # Actual distinct MID and child scalar correlations on the same own word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "RP" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor

theorem nativePoint_value (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
    (p : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
      (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ)
    (i : Fin ((B).parameters.ambient (pairFst ((B).key (C (preparedRoot old R.leftSpec R.rightSpec side))))+1))
    (j : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
      (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)) (h : i.val=j.val) :
    nativePoint old hv hd left right R side p i=p j := by
  unfold nativePoint
  apply congrArg p
  apply Fin.ext
  simpa only [Fin.val_cast] using h

variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
  {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he

theorem SampledLevel.free_count (_S : SampledLevel old hv hd left right R side pMID pChild) :
    (R.orderedFree hk).length=dimension old-depth old := by
  have H := R.orderedFree_length hk
  have HD : (RP).ambient c=dimension old := FormulaSignSlotRadialProviderRetainedAppend.prepared_dimension old e
  have HF := FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd e he
  omega

theorem SampledLevel.local_correlation (S : SampledLevel old hv hd left right R side pMID pChild)
    (b : ℕ) (hb0 : midpointBirth old hv hd left right R≤b) (hb1 : b<finishBirth old hv hd left right R side) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid b=
      nativePoint old hv hd left right R side
        (if b<midpointBirth old hv hd left right R+1+(dimension old-depth old) then pMID else pChild) ⟨FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old R.leftSpec R.rightSpec side)) b,
        FormulaSignSlotRadialProviderAtomic.selected_lt _ _
          (active_after_midpoint old hv hd left right R side b hb0 (hb1.trans_le (finish_le_full old hv hd left right R side)))⟩ := by
  have HK := S.free_count
  have HL : (cs).length=beginBirth old := FormulaSignSlotRadialProviderRetainedAppend.parent_length old hv hd e he
  have HP : (cs).length+R.result.commands.length=midpointBirth old hv hd left right R :=
    congrArg (fun m=>m+R.result.commands.length) HL
  have HG : (FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he).val=depth old+1 := by
    change (FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd e he).labels.length+1=_
    exact congrArg (·+1) (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd e he)
  have HF := finish_eq old hv hd left right R side
  have hgoal (p : Fin ((P).ambient c+1)→ℝ) (j : Fin ((P).ambient c+1))
      (hfield : FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid b=p j)
      (hsel : FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old R.leftSpec R.rightSpec side)) b=j.val) :
      FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid b=
        nativePoint old hv hd left right R side p ⟨FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old R.leftSpec R.rightSpec side)) b,
          FormulaSignSlotRadialProviderAtomic.selected_lt _ _
            (active_after_midpoint old hv hd left right R side b hb0 (hb1.trans_le (finish_le_full old hv hd left right R side)))⟩ :=
    hfield.trans (nativePoint_value old hv hd left right R side p
      ⟨FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old R.leftSpec R.rightSpec side)) b,
        FormulaSignSlotRadialProviderAtomic.selected_lt _ _
          (active_after_midpoint old hv hd left right R side b hb0 (hb1.trans_le (finish_le_full old hv hd left right R side)))⟩ j hsel).symm
  by_cases HM : b=midpointBirth old hv hd left right R
  · have HMPhase : b<midpointBirth old hv hd left right R+1+(dimension old-depth old) := by omega
    simp only [ite_eq_left HMPhase]
    have HV := S.midpoint_anchor_field
    have HE : ((cs).length+R.result.commands.length)=b := by omega
    exact hgoal pMID _ ((congrArg (fun k=>FormulaSignSlotRadialProviderAtomic.bankField
      (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid k) HE).symm.trans HV)
      ((congrArg (FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old R.leftSpec R.rightSpec side))) HM).trans
        ((midpoint_anchor_metadata old hv hd left right R side).2.trans HG.symm))
  by_cases HMC : b<midpointBirth old hv hd left right R+1+(dimension old-depth old)
  · simp only [ite_eq_left HMC]
    let a := b-(midpointBirth old hv hd left right R+1)
    have HA : a<dimension old-depth old := by dsimp only [a];omega
    let k : Fin (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length :=
      ⟨(R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length-1-a,by omega⟩
    have HE : ((cs).length+R.result.commands.length)+1+
        ((R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length-1-k.val)=b := by
      dsimp only [k,a]
      omega
    have HV := S.midpoint_capture_field k
    have HCoord := R.orderedFree_get (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he) k
    have HJ : ((R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).get k).val.val=dimension old-a :=
      HCoord.trans ((congrArg (fun d=>d+1+k.val) (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd e he)).trans
        (by dsimp only [k];omega))
    have HBirth : b=midpointBirth old hv hd left right R+1+a := by dsimp only [a];omega
    exact hgoal pMID _ ((congrArg (fun q=>FormulaSignSlotRadialProviderAtomic.bankField
      (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid q) HE).symm.trans HV)
      (((congrArg (FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old R.leftSpec R.rightSpec side))) HBirth).trans
        (midpoint_capture_metadata old hv hd left right R side a HA).2).trans HJ.symm)
  by_cases HC : b=midpointBirth old hv hd left right R+1+(dimension old-depth old)
  · have HCPhase : ¬b<midpointBirth old hv hd left right R+1+(dimension old-depth old) := by omega
    simp only [ite_eq_right HCPhase]
    have HV := S.child_anchor_field
    have HE : ((cs).length+R.result.commands.length)+1+
        (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length=b := by omega
    exact hgoal pChild _ ((congrArg (fun k=>FormulaSignSlotRadialProviderAtomic.bankField
      (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid k) HE).symm.trans HV)
      ((congrArg (FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old R.leftSpec R.rightSpec side))) HC).trans
        ((child_anchor_metadata old hv hd left right R side).2.trans HG.symm))
  · simp only [ite_eq_right HMC]
    let a := b-(midpointBirth old hv hd left right R+2+(dimension old-depth old))
    have HA : a<dimension old-depth old := by dsimp only [a];omega
    let k : Fin (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length :=
      ⟨(R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length-1-a,by omega⟩
    have HE : ((cs).length+R.result.commands.length)+2+
        (R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length+
          ((R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).length-1-k.val)=b := by
      dsimp only [k,a]
      omega
    have HV := S.child_capture_field k
    have HCoord := R.orderedFree_get (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he) k
    have HJ : ((R.orderedFree (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he)).get k).val.val=dimension old-a :=
      HCoord.trans ((congrArg (fun d=>d+1+k.val) (FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length old hv hd e he)).trans
        (by dsimp only [k];omega))
    have HBirth : b=midpointBirth old hv hd left right R+2+(dimension old-depth old)+a := by dsimp only [a];omega
    exact hgoal pChild _ ((congrArg (fun q=>FormulaSignSlotRadialProviderAtomic.bankField
      (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid q) HE).symm.trans HV)
      (((congrArg (FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old R.leftSpec R.rightSpec side))) HBirth).trans
        (child_capture_metadata old hv hd left right R side a HA).2).trans HJ.symm)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
