/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPhysical
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPhaseValues
/-! # Actual retained local scalars equal their selected physical coordinates -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  parentState parentTuple parentValues parentHom parentCommands parentDescriptor

theorem nativePoint_value (old : List Bool) (e : ℕ)
    (p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ)
    (i : Fin ((B).parameters.ambient (pairFst ((B).key (C (preparedRoot old e))))+1))
    (j : Fin ((P).ambient (preparedRoot old e)+1)) (h : i.val=j.val) :
    nativePoint old e p i=p j := by
  unfold nativePoint
  apply congrArg p
  apply Fin.ext
  simpa only [Fin.val_cast] using h

variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {e : ℕ} {he : e<endBirth (dimension old) (N old) old}
  {p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ}

theorem WordReceipt.free_count (W : WordReceipt old hv hd e he p) :
    (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length=dimension old-depth old := by
  have H := W.local_values_count
  have HC : W.pair.result.commands.length=0 := by
    simpa only [List.length_nil] using congrArg List.length (pair_commands_nil old hv hd e he W.pair)
  have HF := finish_eq old e
  have HP := parent_length old hv hd e he
  omega

theorem WordReceipt.local_correlation (W : WordReceipt old hv hd e he p)
    (b : ℕ) (hb0 : N old+start old≤b) (hb1 : b<finishBirth old e) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid b=
      nativePoint old e p ⟨FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old e)) b,
        FormulaSignSlotRadialProviderAtomic.selected_lt _ _
          (active_after_begin old hv hd e he b hb0 (hb1.trans_le (finish_le_full old hv hd e he)))⟩ := by
  have HK := W.free_count
  have HP : (parentCommands old hv hd e he).length=N old+start old :=
    (parent_length old hv hd e he).trans (begin_eq old)
  have HG : (childCoordinate old hv hd e he).val=depth old+1 := by
    change (parentDescriptor old hv hd e he).labels.length+1=_
    exact congrArg (·+1) (parent_descriptor_length old hv hd e he)
  have HF := finish_eq old e
  have HB := begin_eq old
  have hgoal (j : Fin ((P).ambient (preparedRoot old e)+1))
      (hfield : FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid b=p j)
      (hsel : FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old e)) b=j.val) :
      FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid b=
        nativePoint old e p ⟨FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old e)) b,
          FormulaSignSlotRadialProviderAtomic.selected_lt _ _
            (active_after_begin old hv hd e he b hb0 (hb1.trans_le (finish_le_full old hv hd e he)))⟩ :=
    hfield.trans (nativePoint_value old e p
      ⟨FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old e)) b,
        FormulaSignSlotRadialProviderAtomic.selected_lt _ _
          (active_after_begin old hv hd e he b hb0 (hb1.trans_le (finish_le_full old hv hd e he)))⟩ j hsel).symm
  by_cases HM : b=N old+start old
  · have HV := W.midpoint_anchor_field
    have HE : (parentCommands old hv hd e he).length=b := by omega
    exact hgoal _ ((congrArg (fun k=>FormulaSignSlotRadialProviderAtomic.bankField
      (C (preparedRoot old e)) W.word W.valid k) HE).symm.trans HV)
      ((congrArg (FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old e))) HM).trans
        ((midpoint_anchor_metadata old hv hd e he).2.trans HG.symm))
  by_cases HMC : b<N old+start old+1+(dimension old-depth old)
  · let a := b-(N old+start old+1)
    have HA : a<dimension old-depth old := by dsimp only [a];omega
    let k : Fin (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length :=
      ⟨(W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length-1-a,by omega⟩
    have HE : (parentCommands old hv hd e he).length+1+
        ((W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length-1-k.val)=b := by
      dsimp only [k,a]
      omega
    have HV := W.midpoint_capture_field k
    have HCoord := W.pair.orderedFree_get (parent_descriptor_fit old hv hd e he) k
    have HJ : ((W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).get k).val.val=dimension old-a :=
      HCoord.trans ((congrArg (fun d=>d+1+k.val) (parent_descriptor_length old hv hd e he)).trans
        (by dsimp only [k];omega))
    have HBirth : b=N old+start old+1+a := by dsimp only [a];omega
    exact hgoal _ ((congrArg (fun q=>FormulaSignSlotRadialProviderAtomic.bankField
      (C (preparedRoot old e)) W.word W.valid q) HE).symm.trans HV)
      (((congrArg (FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old e))) HBirth).trans
        (midpoint_capture_metadata old hv hd e he a HA).2).trans HJ.symm)
  by_cases HC : b=N old+start old+1+(dimension old-depth old)
  · have HV := W.child_anchor_field
    have HE : (parentCommands old hv hd e he).length+1+
        (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length=b := by omega
    exact hgoal _ ((congrArg (fun k=>FormulaSignSlotRadialProviderAtomic.bankField
      (C (preparedRoot old e)) W.word W.valid k) HE).symm.trans HV)
      ((congrArg (FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old e))) HC).trans
        ((child_anchor_metadata old hv hd e he).2.trans HG.symm))
  · let a := b-(N old+start old+2+(dimension old-depth old))
    have HA : a<dimension old-depth old := by dsimp only [a];omega
    let k : Fin (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length :=
      ⟨(W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length-1-a,by omega⟩
    have HE : (parentCommands old hv hd e he).length+2+
        (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length+
          ((W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length-1-k.val)=b := by
      dsimp only [k,a]
      omega
    have HV := W.child_capture_field k
    have HCoord := W.pair.orderedFree_get (parent_descriptor_fit old hv hd e he) k
    have HJ : ((W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).get k).val.val=dimension old-a :=
      HCoord.trans ((congrArg (fun d=>d+1+k.val) (parent_descriptor_length old hv hd e he)).trans
        (by dsimp only [k];omega))
    have HBirth : b=N old+start old+2+(dimension old-depth old)+a := by dsimp only [a];omega
    exact hgoal _ ((congrArg (fun q=>FormulaSignSlotRadialProviderAtomic.bankField
      (C (preparedRoot old e)) W.word W.valid q) HE).symm.trans HV)
      (((congrArg (FormulaSignSlotRadialProviderAtomic.selected (C (preparedRoot old e))) HBirth).trans
        (child_capture_metadata old hv hd e he a HA).2).trans HJ.symm)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
