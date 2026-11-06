/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendWordFields
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendSampledLevel
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelScalarValues
/-! # The same sampled proper word reads its distinct midpoint,child and padding values -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits IntegralMixedChronologicalEndpoint
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.preparedRoot preparedRoot
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.depth FormulaSignSlotRadialProviderAtomic.ownBirth
  canonicalObservation compiledProgram fullObservation

section Bounds
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
  (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
theorem compiled_program_length : (compiledProgram old hv hd left right R side).length=
    finishBirth old hv hd left right R side :=
  (congrArg List.length (local_prefix_commands old hv hd left right R side)).symm.trans (paddedPast_length _ _ _)

theorem padded_program_length : fullBirth old hv hd left right R side=
    (compiledProgram old hv hd left right R side).length+
      (IntegralMixedCanonicalPadding.paddingSelections
        ((P).ambient (preparedRoot old R.leftSpec R.rightSpec side)) (tailCount old hv hd left right R side)).length := by
  have H := congrArg List.length (full_commands old hv hd left right R side)
  rw [full_rules_length,List.length_append,List.length_replicate] at H
  rw [IntegralMixedCanonicalPadding.paddingSelections_length]
  change FormulaSignSlotRadialProviderRecordPlan.fullCount (preparedRoot old R.leftSpec R.rightSpec side)=_ at H ⊢
  omega
end Bounds

variable {old : List Bool} {hv : FormulaSignSlotRadialProviderAtomic.Valid old}
  {hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
  {z : ℕ→ℝ} {p0 : Fin ((P).ambient (preparedRoot old R.leftSpec R.rightSpec side)+1)→ℝ}

theorem WordReceipt.local_field (W : WordReceipt old hv hd left right R side z p0)
    (b : ℕ) (hb : b<finishBirth old hv hd left right R side) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side)) W.word W.valid b=
      (canonicalObservation old hv hd left right R side).point z (finishBirth old hv hd left right R side-1-b) := by
  let js := IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old R.leftSpec R.rightSpec side)) (tailCount old hv hd left right R side)
  have HL := compiled_program_length old hv hd left right R side
  have HF := padded_program_length old hv hd left right R side
  let j : Fin (compiledProgram old hv hd left right R side).length := ⟨finishBirth old hv hd left right R side-1-b,by omega⟩
  have HV := W.values ⟨js.length+j.val,by
    change js.length+j.val<(compiledProgram old hv hd left right R side).length+js.length
    have HJ := j.isLt
    omega⟩
  have HO := IntegralMixedPointCompanion.values_old p0
    (fun i=>(canonicalObservation old hv hd left right R side).point z i.val) js j
  have HI : fullBirth old hv hd left right R side-1-b=js.length+j.val := by
    change fullBirth old hv hd left right R side=(compiledProgram old hv hd left right R side).length+js.length at HF
    dsimp only [j]
    omega
  exact (W.field_observation b (hb.trans_le (finish_le_full old hv hd left right R side))).trans
    ((congrArg (fun k=>(fullObservation old hv hd left right R side).point W.tuple k) HI).trans (HV.trans HO))

theorem WordReceipt.padding_field (W : WordReceipt old hv hd left right R side z p0)
    (b : ℕ) (hb0 : finishBirth old hv hd left right R side≤b) (hb1 : b<fullBirth old hv hd left right R side) :
    FormulaSignSlotRadialProviderAtomic.bankField (C (preparedRoot old R.leftSpec R.rightSpec side)) W.word W.valid b=p0 0 := by
  let js := IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old R.leftSpec R.rightSpec side)) (tailCount old hv hd left right R side)
  have HL := compiled_program_length old hv hd left right R side
  have HF := padded_program_length old hv hd left right R side
  have HJ : fullBirth old hv hd left right R side-1-b<js.length := by
    change fullBirth old hv hd left right R side=(compiledProgram old hv hd left right R side).length+js.length at HF
    omega
  let j : Fin js.length := ⟨fullBirth old hv hd left right R side-1-b,HJ⟩
  have HV := W.values ⟨j.val,by
    change j.val<(compiledProgram old hv hd left right R side).length+js.length
    have H := j.isLt
    omega⟩
  have HO := IntegralMixedPointCompanion.values_get p0
    (fun i : Fin (compiledProgram old hv hd left right R side).length=>
      (canonicalObservation old hv hd left right R side).point z i.val) js j
  have HS : (js.get j).val=0 := by
    have HI : j.val<tailCount old hv hd left right R side := by
      simpa only [js,IntegralMixedCanonicalPadding.paddingSelections_length] using j.isLt
    simp only [js,IntegralMixedCanonicalPadding.paddingSelections,List.get_eq_getElem,
      List.getElem_replicate,IntegralMixedCanonicalPadding.zeroFree]
  exact (W.field_observation b hb1).trans (HV.trans (HO.trans (congrArg p0 HS)))

section Local
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he
local notation "g" => FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he
theorem SampledLevel.local_values
    {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
      (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}
    (S : SampledLevel old hv hd left right R side pMID pChild)
    (i : Fin ((cs).length+R.result.commands.length+1+(R.orderedFree hk).length+1+(R.orderedFree hk).length)) :
    (canonicalObservation old hv hd left right R side).point S.localTuple i.val=
      IntegralMixedChronologicalLevelScalarValues.levelValues pMID pChild R.result.nextValues g
        (R.orderedFree hk) i :=
  (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec S.physical))).2.bank_values i
end Local

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
