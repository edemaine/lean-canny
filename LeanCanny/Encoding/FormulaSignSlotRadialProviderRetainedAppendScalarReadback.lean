/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendWordFields
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendLocalReadback
/-! # Chronological scalar readback before and after retained-child completion -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  parentState parentTuple parentValues parentHom parentCommands parentDescriptor levelProgram levelObservation fullObservation

theorem local_program_length (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (R : Pair old hv hd e he) :
    (levelProgram old hv hd e he R false).length=finishBirth old e :=
  (congrArg List.length (local_prefix_commands old hv hd e he R)).symm.trans (paddedPast_length _ _ _)

theorem padded_program_length (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (R : Pair old hv hd e he) :
    fullBirth old e=(levelProgram old hv hd e he R false).length+
      (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old e)) (tailCount old e)).length := by
  have H := congrArg List.length (full_commands old hv hd e he R)
  rw [full_rules_length,List.length_append,List.length_replicate] at H
  rw [IntegralMixedCanonicalPadding.paddingSelections_length]
  change FormulaSignSlotRadialProviderRecordPlan.fullCount (preparedRoot old e)=_ at H ⊢
  omega

variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {e : ℕ} {he : e<endBirth (dimension old) (N old) old}
  {p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ}

theorem WordReceipt.local_field (W : WordReceipt old hv hd e he p)
    (b : ℕ) (hb : b<finishBirth old e) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid b=
      (levelObservation old hv hd e he W.pair false).point W.localTuple (finishBirth old e-1-b) := by
  let js := IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old e)) (tailCount old e)
  have HL := local_program_length old hv hd e he W.pair
  have HF := padded_program_length old hv hd e he W.pair
  let j : Fin (levelProgram old hv hd e he W.pair false).length := ⟨finishBirth old e-1-b,by omega⟩
  have HV := W.full.2.2.2 ⟨js.length+j.val,by
    change js.length+j.val<(levelProgram old hv hd e he W.pair false).length+js.length
    have HJ := j.isLt
    omega⟩
  have HO := IntegralMixedPointCompanion.values_old W.paddingPoint
    (fun i=>(levelObservation old hv hd e he W.pair false).point W.localTuple i.val) js j
  have HI : fullBirth old e-1-b=js.length+j.val := by
    change fullBirth old e=(levelProgram old hv hd e he W.pair false).length+js.length at HF
    dsimp only [j]
    omega
  exact (W.field_observation b (hb.trans_le (finish_le_full old hv hd e he))).trans
    ((congrArg (fun k=>(fullObservation old e).point W.tuple k) HI).trans (HV.trans HO))

theorem WordReceipt.padding_field (W : WordReceipt old hv hd e he p)
    (b : ℕ) (hb0 : finishBirth old e≤b) (hb1 : b<fullBirth old e) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old e)) W.word W.valid b=W.paddingPoint 0 := by
  let js := IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old e)) (tailCount old e)
  have HL := local_program_length old hv hd e he W.pair
  have HF := padded_program_length old hv hd e he W.pair
  have HJ : fullBirth old e-1-b<js.length := by
    change fullBirth old e=(levelProgram old hv hd e he W.pair false).length+js.length at HF
    omega
  let j : Fin js.length := ⟨fullBirth old e-1-b,HJ⟩
  have HV := W.full.2.2.2 ⟨j.val,by
    change j.val<(levelProgram old hv hd e he W.pair false).length+js.length
    have H := j.isLt
    omega⟩
  have HO := IntegralMixedPointCompanion.values_get W.paddingPoint
    (fun i : Fin (levelProgram old hv hd e he W.pair false).length=>
      (levelObservation old hv hd e he W.pair false).point W.localTuple i.val) js j
  have HS : (js.get j).val=0 := by
    have HI : j.val<tailCount old e := by
      simpa only [js,IntegralMixedCanonicalPadding.paddingSelections_length] using j.isLt
    simp only [js,IntegralMixedCanonicalPadding.paddingSelections,List.get_eq_getElem,
      List.getElem_replicate,IntegralMixedCanonicalPadding.zeroFree]
  exact (W.field_observation b hb1).trans (HV.trans (HO.trans (congrArg W.paddingPoint HS)))

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
