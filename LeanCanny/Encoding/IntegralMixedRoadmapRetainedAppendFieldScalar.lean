/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendFieldReadback
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendFieldMetadata
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendSelectionReadback
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPhysical
/-! # Actual selected scalar fields of every fresh retained-append stage -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPointCompanion IntegralMixedFrozenFrame
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (e :ℕ) (he :e<beginBirth hn ht ha hR0 old)
local notation "r"=>preparedRoot hn ht ha hR0 old e
local notation "CTX"=>context hn ht ha hR0 old e
local notation "older"=>parentCommands hn ht ha hR0 old hv hd e he
local notation "js"=>midpointSelections hn ht ha hR0 old hv hd e he
local notation "cs"=>childSelections hn ht ha hR0 old hv hd e he
local notation "loc"=>localInstructions hn ht ha hR0 old hv hd e he
local notation "pads"=>IntegralMixedCanonicalPadding.paddingSelections
  (IntegralCriticalHistoryTask.Parameters.ambient (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)) (preparedRoot hn ht ha hR0 old e))
  (seedTailCount hn ht ha hR0 old e)
local notation "LO"=>localObservation hn ht ha hR0 old hv hd e he
local notation "PV"=>parentValues hn ht ha hR0 old hv hd e he
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedFramedHistoryFamilyBits.family preparedRoot parentCommands parentValues
  midpointSelections childSelections localInstructions localObservation seedTailCount
  IntegralMixedMarkedPrefixFieldReadback.fullObservation IntegralMixedPhysicalFieldEquality.point
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound

private theorem padded_field_value (p p0 :Fin ((P).ambient r+1)→ℝ) (z u :ℕ→ℝ) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S CTX w) (HJ :FieldJoint hn ht ha hR0 old e w hw u)
    (HV :FieldValues hn ht ha hR0 old hv hd e he p p0 z u)
    (b :ℕ) (hb :b<fullBirth hn ht ha hR0 old e) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX w hw b=
      values p0 (fun j :Fin (loc).length=>(LO).point z j.val) pads
        ⟨fullBirth hn ht ha hR0 old e-1-b,by rw [←full_birth_length hn ht ha hR0 old hv hd e he];omega⟩ :=
  (field_observation hn ht ha hR0 old e w hw u HJ b hb).trans (HV.full_values ⟨_,by
    rw [←full_birth_length hn ht ha hR0 old hv hd e he];omega⟩)

private theorem local_field_value (p p0 :Fin ((P).ambient r+1)→ℝ) (z u :ℕ→ℝ) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S CTX w) (HJ :FieldJoint hn ht ha hR0 old e w hw u)
    (HV :FieldValues hn ht ha hR0 old hv hd e he p p0 z u)
    (b :ℕ) (hb :b<finishBirth hn ht ha hR0 old e) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX w hw b=
      (LO).point z ((loc).length-1-b) :=by
  have HL :b<(loc).length:=hb.trans_eq (local_finish hn ht ha hR0 old hv hd e he).symm
  have HF:=full_birth_length hn ht ha hR0 old hv hd e he
  have HFull:=padded_field_value hn ht ha hR0 old hv hd e he p p0 z u w hw HJ HV b (by omega)
  let i :Fin (loc).length:=⟨(loc).length-1-b,by omega⟩
  have HE :fullBirth hn ht ha hR0 old e-1-b=(pads).length+i.val:=by dsimp only [i];omega
  have HI : (⟨fullBirth hn ht ha hR0 old e-1-b,by omega⟩ :Fin ((loc).length+(pads).length))=
      ⟨(pads).length+i.val,by omega⟩:=Fin.ext HE
  exact HFull.trans ((congrArg (values p0 (fun j :Fin (loc).length=>(LO).point z j.val) pads) HI).trans
    (values_old p0 (fun j :Fin (loc).length=>(LO).point z j.val) pads i))

private theorem midpoint_field_numeric (p p0 :Fin ((P).ambient r+1)→ℝ) (z u :ℕ→ℝ) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S CTX w) (HJ :FieldJoint hn ht ha hR0 old e w hw u)
    (HV :FieldValues hn ht ha hR0 old hv hd e he p p0 z u)
    (b :ℕ) (hb0 :(older).length≤b) (hb1 :b<(older).length+(js).length) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX w hw b=
      p ((js).get ⟨(older).length+(js).length-1-b,by omega⟩).val :=by
  have HL:=local_length hn ht ha hR0 old hv hd e he
  have HF:=local_finish hn ht ha hR0 old hv hd e he
  have HObs:=local_field_value hn ht ha hR0 old hv hd e he p p0 z u w hw HJ HV b (by omega)
  let i :Fin ((older).length+(js).length):=⟨(older).length+(js).length-1-b,by omega⟩
  let j :Fin (js).length:=⟨(older).length+(js).length-1-b,by omega⟩
  have HE :(loc).length-1-b=(cs).length+i.val:=by dsimp only [i];omega
  have HEFin : (⟨(loc).length-1-b,by omega⟩ :Fin ((older).length+(js).length+(cs).length))=
      ⟨(cs).length+i.val,by omega⟩:=Fin.ext HE
  have HVL:=HV.local_values ⟨(loc).length-1-b,by omega⟩
  have HVO:=values_old p (values p PV js) cs i
  have HVJ:=values_get p PV js j
  exact HObs.trans (HVL.trans ((congrArg (values p (values p PV js) cs) HEFin).trans (HVO.trans HVJ)))

private theorem child_field_numeric (p p0 :Fin ((P).ambient r+1)→ℝ) (z u :ℕ→ℝ) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S CTX w) (HJ :FieldJoint hn ht ha hR0 old e w hw u)
    (HV :FieldValues hn ht ha hR0 old hv hd e he p p0 z u)
    (b :ℕ) (hb0 :(older).length+(js).length≤b) (hb1 :b<finishBirth hn ht ha hR0 old e) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX w hw b=
      p ((cs).get ⟨(older).length+(js).length+(cs).length-1-b,by
        have HL:=local_length hn ht ha hR0 old hv hd e he
        have HF:=local_finish hn ht ha hR0 old hv hd e he
        omega⟩).val :=by
  have HL:=local_length hn ht ha hR0 old hv hd e he
  have HF:=local_finish hn ht ha hR0 old hv hd e he
  have HObs:=local_field_value hn ht ha hR0 old hv hd e he p p0 z u w hw HJ HV b hb1
  let j :Fin (cs).length:=⟨(older).length+(js).length+(cs).length-1-b,by omega⟩
  have HE :(loc).length-1-b=j.val:=by dsimp only [j];omega
  have HEFin : (⟨(loc).length-1-b,by omega⟩ :Fin ((older).length+(js).length+(cs).length))=
      ⟨j.val,by omega⟩:=Fin.ext HE
  have HVL:=HV.local_values ⟨(loc).length-1-b,by omega⟩
  exact HObs.trans (HVL.trans ((congrArg (values p (values p PV js) cs) HEFin).trans
    (values_get p (values p PV js) cs j)))

private theorem padding_field_numeric (p p0 :Fin ((P).ambient r+1)→ℝ) (z u :ℕ→ℝ) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S CTX w) (HJ :FieldJoint hn ht ha hR0 old e w hw u)
    (HV :FieldValues hn ht ha hR0 old hv hd e he p p0 z u)
    (b :ℕ) (hb0 :finishBirth hn ht ha hR0 old e≤b) (hb1 :b<fullBirth hn ht ha hR0 old e) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX w hw b=p0 0 :=by
  have HL:=local_finish hn ht ha hR0 old hv hd e he
  have HF:=full_birth_length hn ht ha hR0 old hv hd e he
  have HObs:=padded_field_value hn ht ha hR0 old hv hd e he p p0 z u w hw HJ HV b hb1
  let j :Fin (pads).length:=⟨fullBirth hn ht ha hR0 old e-1-b,by omega⟩
  have HVJ:=values_get p0 (fun j :Fin (loc).length=>(LO).point z j.val) pads j
  apply HObs.trans
  apply HVJ.trans
  apply congrArg p0
  simp only [IntegralMixedCanonicalPadding.paddingSelections,List.get_eq_getElem,List.getElem_replicate,
    IntegralMixedCanonicalPadding.zeroFree]

theorem scalar_of_field_values (p p0 :Fin ((P).ambient r+1)→ℝ) (z u :ℕ→ℝ) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S CTX w) (HJ :FieldJoint hn ht ha hR0 old e w hw u)
    (HV :FieldValues hn ht ha hR0 old hv hd e he p p0 z u)
    (b :ℕ) (hb0 :beginBirth hn ht ha hR0 old≤b) (hb1 :b<fullBirth hn ht ha hR0 old e)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false CTX b) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX w hw b=
      (if b<finishBirth hn ht ha hR0 old e then nativePoint hn ht ha hR0 old e p
        else nativePoint hn ht ha hR0 old e p0)
        ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false CTX b,
          IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ hb⟩ :=by
  by_cases hFresh :b<finishBirth hn ht ha hR0 old e
  · rw [ite_eq_left hFresh]
    have HB0 :(older).length≤b:=by rw [parent_length];exact hb0
    by_cases hMid :b<(older).length+(js).length
    · let i :Fin (js).length:=⟨(older).length+(js).length-1-b,by omega⟩
      have HR :(older).length+(js).length-1-i.val=b:=by dsimp only [i];omega
      have HS:=midpoint_selection_selected hn ht ha hR0 old hv hd e he i
      have HNat :IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false CTX b=
          ((js).get i).val.val :=
        (congrArg (IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false CTX) HR.symm).trans HS
      apply (midpoint_field_numeric hn ht ha hR0 old hv hd e he p p0 z u w hw HJ HV b HB0 hMid).trans
      unfold nativePoint
      apply congrArg p
      exact Fin.ext HNat.symm
    · have HL:=local_length hn ht ha hR0 old hv hd e he
      have HF:=local_finish hn ht ha hR0 old hv hd e he
      let i :Fin (cs).length:=⟨(older).length+(js).length+(cs).length-1-b,by omega⟩
      have HR :(older).length+(js).length+(cs).length-1-i.val=b:=by dsimp only [i];omega
      have HS:=child_selection_selected hn ht ha hR0 old hv hd e he i
      have HNat :IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false CTX b=
          ((cs).get i).val.val :=
        (congrArg (IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false CTX) HR.symm).trans HS
      apply (child_field_numeric hn ht ha hR0 old hv hd e he p p0 z u w hw HJ HV b (by omega) hFresh).trans
      unfold nativePoint
      apply congrArg p
      exact Fin.ext HNat.symm
  · rw [ite_eq_right hFresh]
    have HS:=seed_selected_after_finish hn ht ha hR0 old hv hd e he b (by omega) hb1
    apply (padding_field_numeric hn ht ha hR0 old hv hd e he p p0 z u w hw HJ HV b (by omega) hb1).trans
    unfold nativePoint
    apply congrArg p0
    exact Fin.ext HS.symm

theorem scalar_of_word_receipt (p p0 :Fin ((P).ambient r+1)→ℝ)
    (W :WordReceipt hn ht ha hR0 old hv hd e he p p0)
    (b :ℕ) (hb0 :beginBirth hn ht ha hR0 old≤b) (hb1 :b<fullBirth hn ht ha hR0 old e)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false CTX b) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX W.word W.valid b=
      (if b<finishBirth hn ht ha hR0 old e then nativePoint hn ht ha hR0 old e p
        else nativePoint hn ht ha hR0 old e p0)
        ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false CTX b,
          IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ hb⟩ :=by
  have HJ :FieldJoint hn ht ha hR0 old e W.word W.valid W.tuple:=W.joint
  have HV :FieldValues hn ht ha hR0 old hv hd e he p p0 W.localTuple W.tuple:=⟨W.local_values,W.values⟩
  exact scalar_of_field_values hn ht ha hR0 old hv hd e he p p0 W.localTuple W.tuple
    W.word W.valid HJ HV b hb0 hb1 hb

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
