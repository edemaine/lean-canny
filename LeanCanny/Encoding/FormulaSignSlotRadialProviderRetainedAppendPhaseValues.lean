/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendScalarReadback
/-! # Both retained scalar capture blocks read the actual chosen coordinates -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedChronologicalLevelScalarValues
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "RP" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  parentState parentTuple parentValues parentHom parentCommands parentDescriptor levelProgram levelObservation
variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {e : ℕ} {he : e<endBirth (dimension old) (N old) old}
  {p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ}

theorem WordReceipt.local_values_count (W : WordReceipt old hv hd e he p) :
    (parentCommands old hv hd e he).length+W.pair.result.commands.length+1+
      (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length+1+
      (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length=finishBirth old e := by
  have HC : W.pair.result.commands.length=0 := by
    simpa only [List.length_nil] using congrArg List.length (pair_commands_nil old hv hd e he W.pair)
  have HK := W.pair.orderedFree_length (parent_descriptor_fit old hv hd e he)
  have HD : (RP).ambient (preparedRoot old e)=dimension old := prepared_dimension old e
  have HF := parent_descriptor_length old hv hd e he
  have HE := finish_eq old e
  have HL := parent_length old hv hd e he
  omega

theorem WordReceipt.local_value_at (W : WordReceipt old hv hd e he p)
    (i : Fin ((parentCommands old hv hd e he).length+W.pair.result.commands.length+1+
      (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length+1+
      (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length)) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid
      (finishBirth old e-1-i.val)=levelValues p p W.pair.result.nextValues
        (childCoordinate old hv hd e he) (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)) i := by
  have HI := i.isLt.trans_eq W.local_values_count
  have H := W.local_field (finishBirth old e-1-i.val) (by omega)
  have HE : finishBirth old e-1-(finishBirth old e-1-i.val)=i.val := by omega
  exact H.trans ((congrArg (fun k=>(levelObservation old hv hd e he W.pair false).point W.localTuple k) HE).trans
    (W.local_values i))

theorem WordReceipt.child_anchor_field (W : WordReceipt old hv hd e he p) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid
      ((parentCommands old hv hd e he).length+1+(W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length)=
      p (childCoordinate old hv hd e he) := by
  have HC : W.pair.result.commands.length=0 := by
    simpa only [List.length_nil] using congrArg List.length (pair_commands_nil old hv hd e he W.pair)
  have HF := W.local_values_count
  have H := W.local_value_at ⟨(W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length,by omega⟩
  have HV := IntegralMixedChronologicalLevelScalarValues.child_anchor p p W.pair.result.nextValues (childCoordinate old hv hd e he)
    (W.pair.orderedFree (parent_descriptor_fit old hv hd e he))
  have HE : finishBirth old e-1-(W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length=
      (parentCommands old hv hd e he).length+1+(W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length := by omega
  exact (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid b) HE).symm.trans
    (H.trans HV)

theorem WordReceipt.midpoint_anchor_field (W : WordReceipt old hv hd e he p) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid
      (parentCommands old hv hd e he).length=p (childCoordinate old hv hd e he) := by
  have HC : W.pair.result.commands.length=0 := by
    simpa only [List.length_nil] using congrArg List.length (pair_commands_nil old hv hd e he W.pair)
  have HF := W.local_values_count
  have H := W.local_value_at ⟨(W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length+1+
    (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length,by omega⟩
  have HV := IntegralMixedChronologicalLevelScalarValues.midpoint_anchor p p W.pair.result.nextValues (childCoordinate old hv hd e he)
    (W.pair.orderedFree (parent_descriptor_fit old hv hd e he))
  have HE : finishBirth old e-1-((W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length+1+
      (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length)=(parentCommands old hv hd e he).length := by omega
  exact (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid b) HE).symm.trans
    (H.trans HV)

theorem WordReceipt.child_capture_field (W : WordReceipt old hv hd e he p)
    (k : Fin (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid
      ((parentCommands old hv hd e he).length+2+(W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length+
        ((W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length-1-k.val))=
      p ((W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).get k).val := by
  have HC : W.pair.result.commands.length=0 := by
    simpa only [List.length_nil] using congrArg List.length (pair_commands_nil old hv hd e he W.pair)
  have HF := W.local_values_count
  have HK := k.isLt
  have H := W.local_value_at ⟨k.val,by omega⟩
  have HV := IntegralMixedChronologicalLevelScalarValues.child_capture p p W.pair.result.nextValues (childCoordinate old hv hd e he)
    (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)) k
  have HE : finishBirth old e-1-k.val=(parentCommands old hv hd e he).length+2+
      (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length+
        ((W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length-1-k.val) := by omega
  exact (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid b) HE).symm.trans
    (H.trans HV)

theorem WordReceipt.midpoint_capture_field (W : WordReceipt old hv hd e he p)
    (k : Fin (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid
      ((parentCommands old hv hd e he).length+1+
        ((W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length-1-k.val))=
      p ((W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).get k).val := by
  have HC : W.pair.result.commands.length=0 := by
    simpa only [List.length_nil] using congrArg List.length (pair_commands_nil old hv hd e he W.pair)
  have HF := W.local_values_count
  have HK := k.isLt
  have H := W.local_value_at ⟨(W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length+1+k.val,by omega⟩
  have HV := IntegralMixedChronologicalLevelScalarValues.midpoint_capture p p W.pair.result.nextValues (childCoordinate old hv hd e he)
    (W.pair.orderedFree (parent_descriptor_fit old hv hd e he)) k
  have HE : finishBirth old e-1-((W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length+1+k.val)=
      (parentCommands old hv hd e he).length+1+
        ((W.pair.orderedFree (parent_descriptor_fit old hv hd e he)).length-1-k.val) := by omega
  exact (congrArg (fun b=>FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid b) HE).symm.trans
    (H.trans HV)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
