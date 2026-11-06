/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendCaptures
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendCodes
/-! # The literal appended bytes execute the constructed retained level -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalEndpoint
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "cap" => FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap

private theorem append_raw_middle (n : ℕ) (q l r : List Bool) (side : Bool) (p : List Bool) (i : ℕ)
    (hi : i<(IntegralMixedRoadmapLevel.codes n (IntegralMixedRoadmapLevel.packet
      (IntegralMixedRoadmapChain.frozen q (IntegralMixedRoadmapChain.depth q)) l r side [])).length) :
    WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapChain.appendPayload n q l r side p))
      (IntegralMixedRoadmapChain.rawStart n q (IntegralMixedRoadmapChain.depth q)+i)=
        ((IntegralMixedRoadmapLevel.codes n (IntegralMixedRoadmapLevel.packet
          (IntegralMixedRoadmapChain.frozen q (IntegralMixedRoadmapChain.depth q)) l r side []))[i]?).getD [] := by
  let q' := IntegralMixedRoadmapChain.appendPayload n q l r side p
  have HD : IntegralMixedRoadmapChain.depth q'=IntegralMixedRoadmapChain.depth q+1 :=
    IntegralMixedRoadmapChain.append_depth n q l r side p
  obtain ⟨before,after,HE,HL⟩ := IntegralMixedRoadmapChain.compiledCodes_split n q'
    (IntegralMixedRoadmapChain.depth q) (by omega)
  rw [IntegralMixedRoadmapChain.append_template_last n q l r side p] at HE
  rw [IntegralMixedRoadmapChain.append_rawStart_before n q l r side p
    (IntegralMixedRoadmapChain.depth q) le_rfl] at HL
  have HR : IntegralMixedRoadmapChain.raw q'=IntegralMixedRoadmapChain.compiled n q' :=
    IntegralMixedRoadmapChain.completePayload_raw n _ p
  change WordList.get (IntegralMixedRoadmapChain.raw q') _=_
  rw [HR,IntegralMixedRoadmapChain.compiled,HE,←HL,WordList.get_encode,List.append_assoc,
    List.getElem?_append_right (by omega),Nat.add_sub_cancel_left,List.getElem?_append_left hi]

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderIntegerSource.source parentState parentTuple parentHom parentValues parentDescriptor

theorem prepared_code (old : List Bool) (e i : ℕ) :
    IntegralMixedCausalRecordPlanBits.code (preparedRoot old e) i=
      WordList.get (IntegralMixedRoadmapChain.raw (payload (dimension old) old e)) i := by
  unfold preparedRoot
  rw [FormulaSignSlotRadialProviderAtomic.root_record_code,payload_packet]

section Level
variable (old : List Bool) (hv : A old) (hd : depth old<dimension old)
  (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (R : Pair old hv hd e he)

theorem local_codes_compiled :
    (R.levelCodes (parent_descriptor_fit old hv hd e he) (childCoordinate old hv hd e he)
      (child_coordinate_free old hv hd e he) false).reverse=
      IntegralMixedRoadmapLevel.codes (dimension old) (IntegralMixedRoadmapLevel.packet
        (FormulaSignSlotRadialProviderAtomic.frozen old) (endpoint e) (endpoint e) false []) := by
  have H := congrArg WordListRecords.decode (level_codes old hv hd e he R)
  simpa only [IntegralMixedRoadmapLevel.compiled,WordListRecords.decode_encode] using H

theorem local_codes_length :
    (R.levelCodes (parent_descriptor_fit old hv hd e he) (childCoordinate old hv hd e he)
      (child_coordinate_free old hv hd e he) false).length=2+2*(dimension old-depth old) := by
  have HC := R.levelCodes_length (parent_descriptor_fit old hv hd e he) (childCoordinate old hv hd e he)
    (child_coordinate_free old hv hd e he) false
  have HN := pair_commands_nil old hv hd e he R
  have HF := R.orderedFree_length (parent_descriptor_fit old hv hd e he)
  have HD : FormulaSignSlotRadialProviderRecordPlan.parameters.ambient (preparedRoot old e)=dimension old :=
    prepared_dimension old e
  have HK := parent_descriptor_length old hv hd e he
  rw [HN,List.length_nil] at HC
  omega

attribute [local irreducible] preparedRoot start IntegralMixedCausalRecordPlanBits.code
  IntegralMixedCausalRecordPlanBits.records IntegralMixedRoadmapChain.raw IntegralMixedRoadmapLevel.codes
  NativePair.levelCodes FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.payload FormulaSignSlotRadialProviderAtomic.depth
  FormulaSignSlotRadialProviderAtomic.frozen FormulaSignSlotRadialProviderAtomic.root

theorem local_code_at (i : ℕ)
    (hi : i<(R.levelCodes (parent_descriptor_fit old hv hd e he) (childCoordinate old hv hd e he)
      (child_coordinate_free old hv hd e he) false).length) :
    IntegralMixedCausalRecordPlanBits.code (preparedRoot old e) (start old+i)=
      (((R.levelCodes (parent_descriptor_fit old hv hd e he) (childCoordinate old hv hd e he)
        (child_coordinate_free old hv hd e he) false).reverse)[i]?).getD [] := by
  have HL := local_codes_compiled old hv hd e he R
  have HI : i<(IntegralMixedRoadmapLevel.codes (dimension old) (IntegralMixedRoadmapLevel.packet
      (FormulaSignSlotRadialProviderAtomic.frozen old) (endpoint e) (endpoint e) false [])).length := by
    rw [←HL,List.length_reverse]
    exact hi
  have H := append_raw_middle (dimension old) (FormulaSignSlotRadialProviderAtomic.payload old)
    (endpoint e) (endpoint e) false (IntegralMixedRoadmapChain.seedCode (dimension old)) i
    (by simpa only [FormulaSignSlotRadialProviderAtomic.frozen,FormulaSignSlotRadialProviderAtomic.depth] using HI)
  have HF : IntegralMixedRoadmapChain.frozen (FormulaSignSlotRadialProviderAtomic.payload old)
      (IntegralMixedRoadmapChain.depth (FormulaSignSlotRadialProviderAtomic.payload old))=
        FormulaSignSlotRadialProviderAtomic.frozen old := by
    unfold FormulaSignSlotRadialProviderAtomic.frozen FormulaSignSlotRadialProviderAtomic.depth
    rfl
  rw [HF,←HL] at H
  rw [prepared_code]
  simpa only [payload,start,FormulaSignSlotRadialProviderAtomic.depth] using H

theorem local_finish_index : FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+start old+
    (R.levelCodes (parent_descriptor_fit old hv hd e he) (childCoordinate old hv hd e he)
      (child_coordinate_free old hv hd e he) false).length=finishBirth old e := by
  rw [local_codes_length,prepared_initial,finish_eq]
  have HB := parent_length old hv hd e he
  have HC := FormulaSignSlotRadialProviderRecordContinuation.beforeCommands_length (preparedRoot old e)
    (start old) (prefix_fit old hv hd e he)
  change (parentCommands old hv hd e he).length=
    FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+start old at HC
  rw [prepared_initial] at HC
  omega

theorem local_code_fit : start old+
    (R.levelCodes (parent_descriptor_fit old hv hd e he) (childCoordinate old hv hd e he)
      (child_coordinate_free old hv hd e he) false).length≤IntegralMixedCausalRecordPlanBits.count (preparedRoot old e) := by
  have HF := finish_le_full old hv hd e he
  rw [←local_finish_index old hv hd e he R] at HF
  change _≤FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+
    IntegralMixedCausalRecordPlanBits.count (preparedRoot old e) at HF
  omega

theorem parent_state_start : parentState old hv hd e he=
    FormulaSignSlotRadialProviderRecordContinuation.beforeState (preparedRoot old e) (start old)
      (prefix_fit old hv hd e he) := by
  unfold parentState parentCommands FormulaSignSlotRadialProviderRecordContinuation.beforeState
    FormulaSignSlotRadialProviderRecordContinuation.beforeCommands IntegralMixedStaticRecordContinuation.prefixStart
    IntegralMixedCausalUnitContinuation.start
  rfl

theorem local_prefix_commands : paddedPast (defaultInstruction P D (preparedRoot old e))
    ((D).rules (preparedRoot old e)) (finishBirth old e)=levelProgram old hv hd e he R false := by
  have HR := R.level_room (parent_descriptor_fit old hv hd e he) (childCoordinate old hv hd e he)
    (child_coordinate_free old hv hd e he) false (by have H := pair_level_room old hv hd e he R;omega)
  have HD := R.level_decodes (parent_descriptor_fit old hv hd e he) (childCoordinate old hv hd e he)
    (child_coordinate_free old hv hd e he) false HR
  have HD' := (IntegralMixedOptionalEndpoints.Decodes.congr_start (parentState old hv hd e he)
    (FormulaSignSlotRadialProviderRecordContinuation.beforeState (preparedRoot old e) (start old)
      (prefix_fit old hv hd e he)) rfl rfl (heq_of_eq (parent_state_start old hv hd e he))
    (FormulaSignSlotRadialProviderRecordPlan.positive (preparedRoot old e)) (cap (preparedRoot old e))
    _ HR HR _).mp HD
  have H := FormulaSignSlotRadialProviderRecordContinuation.compiled_commands (preparedRoot old e) (start old)
    (prefix_fit old hv hd e he) _ (local_code_fit old hv hd e he R) (local_code_at old hv hd e he R) _ HR HD'
  rw [local_finish_index old hv hd e he R] at H
  exact H

end Level
end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
