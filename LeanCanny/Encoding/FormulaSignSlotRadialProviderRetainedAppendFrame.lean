/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendParent
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixFields
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendProgram
/-! # The actual retained parent descriptor reads the old chronological fields -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial)
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial

theorem parent_frame_good (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    IntegralMixedChronologicalFrameCode.Good ((P).ambient (preparedRoot old e))
      (parentCommands old hv hd e he).length (FormulaSignSlotRadialProviderAtomic.frozen old) := by
  rw [parent_length,prepared_dimension]
  exact IntegralMixedRoadmapLevel.frame_mono (FormulaSignSlotRadialProviderAtomic.own_frame_good old hv)
    (Nat.sub_le _ _)

noncomputable def parentDescriptor (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :=
  IntegralMixedChronologicalFrameCode.descriptor ((P).ambient (preparedRoot old e))
    (parentCommands old hv hd e he).length (FormulaSignSlotRadialProviderAtomic.frozen old)
    (parent_frame_good old hv hd e he)

theorem parent_labels (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    IntegralMixedChronologicalFrameCode.labels (parentDescriptor old hv hd e he)=
      FormulaSignSlotRadialProviderAtomic.frozen old :=
  IntegralMixedRoadmapRetainedAppend.descriptor_frozen_labels _ _ _ _ (parent_frame_good old hv hd e he)

theorem parent_descriptor_length (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    (parentDescriptor old hv hd e he).labels.length=depth old := by
  simp only [parentDescriptor,IntegralMixedChronologicalFrameCode.descriptor_length,
    FormulaSignSlotRadialProviderAtomic.frozen_count]

theorem parent_descriptor_nonterminal (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    (parentDescriptor old hv hd e he).labels.length<(P).ambient (preparedRoot old e) := by
  rw [parent_descriptor_length,prepared_dimension]
  exact hd

theorem parent_descriptor_fit (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    (parentDescriptor old hv hd e he).labels.length<(P).ambient (preparedRoot old e)+1 :=
  (parent_descriptor_nonterminal old hv hd e he).trans (Nat.lt_succ_self _)

noncomputable def endpointLabel (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) : Fin (parentCommands old hv hd e he).length :=
  ⟨e,by rw [parent_length];exact he⟩

noncomputable def parentValues (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :=
  IntegralMixedFullBankPoint.point (parentState old hv hd e he) (parentTuple old hv hd e he)

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPlan.bank parentCommands parentState parentTuple parentValues
  FormulaSignSlotRadialProviderRecordPrefix.observation

theorem parent_values (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (i : Fin (parentCommands old hv hd e he).length) :
    parentValues old hv hd e he i=
      FormulaSignSlotRadialProviderAtomic.field old hv ((parentCommands old hv hd e he).length-1-i.val) := by
  have HP := IntegralMixedFramedRunObservation.point_actual (initial P D (preparedRoot old e))
    (parentCommands old hv hd e he) (parent_room old hv hd e he) (oldNatural old hv) i
  have HPoint : parentValues old hv hd e he i=
      (IntegralMixedFramedRunObservation.ofCommands (initial P D (preparedRoot old e))
        (parentCommands old hv hd e he) (parent_room old hv hd e he)).point (oldNatural old hv) i.val := by
    unfold parentValues parentState parentTuple
    exact HP.symm
  have HO := parent_observation old hv hd e he
  have HE := prefix_observation old hv hd e he (start old) (Nat.le_refl _)
  have HA := congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.point (oldNatural old hv) i.val)
    (HO.symm.trans HE)
  have HL : (parentCommands old hv hd e he).length=
      FormulaSignSlotRadialProviderRecordPlan.count (FormulaSignSlotRadialProviderAtomic.root old)+start old :=
    parent_length old hv hd e he
  have HV := FormulaSignSlotRadialProviderRecordPrefix.word_value
    (FormulaSignSlotRadialProviderAtomic.root old) (FormulaSignSlotRadialProviderAtomic.word old)
    (FormulaSignSlotRadialProviderAtomic.full_valid old hv) (start old) (start_fit old hv) i.val
      (i.isLt.trans_eq HL)
  rw [←HL] at HV
  exact HPoint.trans (HA.trans HV)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
