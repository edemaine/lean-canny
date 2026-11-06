/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendRecords
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendParentColumns
public import LeanCanny.Algebra.IntegralMixedPrefixProgramTransport
/-! # The guarded canonical program executes in the actual new provider root -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e
local notation "oldCs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "x" => FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd e he
local notation "d" => FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd e he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he
local notation "g" => FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he
local notation "hg" => FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd e he
local notation "Q" root => FormulaSignSlotRadialProviderRecordPlan.spatial root
local notation "D" => FormulaSignSlotRadialProviderAtomic.dimension old
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial old

local notation "PLAN" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
variable (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
local notation "good" => endpoints_good old hv hd left right R
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side
local notation "j" => start old
local notation "hj" => prefix_fit old hv hd R.leftSpec R.rightSpec side good
local notation "newCs" => parentCommands old hv hd R.leftSpec R.rightSpec side good
local notation "newX" => parentState old hv hd R.leftSpec R.rightSpec side good
local notation "startX" => FormulaSignSlotRadialProviderRecordContinuation.beforeState r j hj
open IntegralMixedFramedHistoryFamilyBits (defaultInstruction)
noncomputable local instance providerProperPlanOldIndexFintype : Fintype (Index (Fin 0) oldCs) := indexFintype (Fin 0) oldCs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.depth

theorem constructed_parent_snapshot : IntegralMixedPrefixSnapshot.ofState newX=
    IntegralMixedPrefixSnapshot.ofState startX := by
  unfold parentState parentCommands FormulaSignSlotRadialProviderRecordContinuation.beforeState
    FormulaSignSlotRadialProviderRecordContinuation.beforeCommands IntegralMixedStaticRecordContinuation.prefixStart
    IntegralMixedCausalUnitContinuation.start
  rfl

noncomputable def canonicalStartSnapshot := IntegralMixedPrefixSnapshot.ofState x
noncomputable def actualStartSnapshot := IntegralMixedPrefixSnapshot.ofState startX

theorem start_snapshot_eq : actualStartSnapshot old hv hd left right R side=canonicalStartSnapshot old hv hd := by
  have HE := constructed_parent_snapshot old hv hd left right R side
  exact HE.symm.trans (parent_snapshot_eq old hv hd R.leftSpec R.rightSpec side good)

noncomputable def localProgram : List (IntegralMixedFullHistoryScript.Command (Q r) ((P).width r)) :=
  (canonicalStartSnapshot old hv hd).castProgram
    (start_snapshot_eq old hv hd left right R side).symm (R.levelCommands hk g hg side)

theorem local_program_length :(localProgram old hv hd left right R side).length=
    (R.levelCommands hk g hg side).length:=
  IntegralMixedPrefixSnapshot.Data.castProgram_length _ _

theorem local_program_heq :HEq (localProgram old hv hd left right R side)
    (R.levelCommands hk g hg side):=IntegralMixedPrefixSnapshot.Data.castProgram_heq _ _

theorem level_code_command_count :(R.levelCodes hk g hg side).length=(R.levelCommands hk g hg side).length:=by
  rw [R.levelCodes_length,R.levelCommands_length]



theorem local_program_room :
    (FormulaSignSlotRadialProviderRecordContinuation.beforeCommands r j hj).length+
      (localProgram old hv hd left right R side).length≤(P).cap r+1+1 := by
  have HB := FormulaSignSlotRadialProviderRecordPrefix.bound r
    (j+(R.levelCodes hk g hg side).length) (local_code_fit old hv hd left right R side)
  rw [FormulaSignSlotRadialProviderRecordContinuation.beforeCommands_length,
    local_program_length,←level_code_command_count old hv hd left right R side]
  omega

theorem canonical_program_room :(oldCs).length+(R.levelCommands hk g hg side).length≤(P).cap c+1+1:=by
  have HR:=local_program_room old hv hd left right R side
  exact (IntegralMixedPrefixSnapshot.Data.castProgram_room
    (start_snapshot_eq old hv hd left right R side).symm (R.levelCommands hk g hg side)).mpr HR

noncomputable local instance providerProperPlanCanonicalIndexFintype :Fintype (canonicalStartSnapshot old hv hd).index:=by
  change Fintype (Index (Fin 0) oldCs)
  exact indexFintype (Fin 0) oldCs

noncomputable local instance providerProperPlanActualIndexFintype :Fintype (actualStartSnapshot old hv hd left right R side).index:=by
  change Fintype (Index (Fin 0) (FormulaSignSlotRadialProviderRecordContinuation.beforeCommands r j hj))
  exact indexFintype (Fin 0) _

attribute [local irreducible] IntegralMixedOptionalEndpoints.Decodes
  IntegralMixedFullHistoryScript.continueRun IntegralMixedPrefixSnapshot.Data.castProgram
  NativePair.levelCommands NativePair.levelCodes

theorem local_decodes :Decodes startX (FormulaSignSlotRadialProviderRecordPlan.positive r)
    (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap r)
    (localProgram old hv hd left right R side)
    (local_program_room old hv hd left right R side) (R.levelCodes hk g hg side):=by
  have HD:=R.level_decodes hk g hg side (canonical_program_room old hv hd left right R side)
  have HC:=@IntegralMixedPrefixSnapshot.Data.decodes_cast
    (canonicalStartSnapshot old hv hd)
    (actualStartSnapshot old hv hd left right R side) inferInstance inferInstance
    (start_snapshot_eq old hv hd left right R side).symm
    (FormulaSignSlotRadialProviderRecordPlan.positive c)
    (FormulaSignSlotRadialProviderRecordPlan.positive r)
    (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap c)
    (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap r)
    (R.levelCommands hk g hg side) (canonical_program_room old hv hd left right R side)
    (local_program_room old hv hd left right R side) (R.levelCodes hk g hg side)
  have HR:=HC.mp HD
  convert HR using 1 <;> rfl

theorem local_run_heq :HEq
    (IntegralMixedFullHistoryScript.continueRun x (R.levelCommands hk g hg side)
      (canonical_program_room old hv hd left right R side))
    (IntegralMixedFullHistoryScript.continueRun startX (localProgram old hv hd left right R side)
      (local_program_room old hv hd left right R side)):=
  IntegralMixedPrefixSnapshot.Data.continueRun_cast
    (start_snapshot_eq old hv hd left right R side).symm (R.levelCommands hk g hg side)
    (canonical_program_room old hv hd left right R side)
    (local_program_room old hv hd left right R side)

noncomputable def compiledProgram :List (Instruction ((P).ambient r) ((P).width r)):=
  List.append ((localProgram old hv hd left right R side).map
    (IntegralMixedFramedFixedContinuation.wrap (Q r)
      (IntegralMixedStaticRecordPrefix.cap (Q r) (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap r)))) newCs

noncomputable def canonicalCompiledProgram :List (Instruction ((P).ambient c) ((P).width c)):=
  List.append ((R.levelCommands hk g hg side).map (IntegralMixedFramedFixedContinuation.wrap (Q c)
    (IntegralMixedStaticRecordPrefix.cap (Q c) (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap c)))) oldCs

theorem compiled_program_heq :HEq (compiledProgram old hv hd left right R side)
    (canonicalCompiledProgram old hv hd left right R side):=by
  have H:=IntegralMixedPrefixSnapshot.Data.wrappedAppend_cast
    (start_snapshot_eq old hv hd left right R side).symm
    (IntegralMixedStaticRecordPrefix.cap (Q c) (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap c))
    (IntegralMixedStaticRecordPrefix.cap (Q r) (FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap r))
    (R.levelCommands hk g hg side) oldCs newCs
    (parent_commands_heq old hv hd R.leftSpec R.rightSpec side good).symm
  convert H.symm using 1 <;> rfl

noncomputable def finishBirth:=beginBirth old+(R.levelCodes hk g hg side).length

theorem local_prefix_commands : paddedPast (defaultInstruction P PLAN r) ((PLAN).rules r)
    (finishBirth old hv hd left right R side)=compiledProgram old hv hd left right R side := by
  have HC := FormulaSignSlotRadialProviderRecordContinuation.compiled_commands r j hj
    (R.levelCodes hk g hg side) (local_code_fit old hv hd left right R side)
    (local_code_at old hv hd left right R side)
    (localProgram old hv hd left right R side)
    (local_program_room old hv hd left right R side)
    (local_decodes old hv hd left right R side)
  have HB : FormulaSignSlotRadialProviderRecordPlan.count r+j=beginBirth old := by
    rw [prepared_initial,begin_eq_start]
  rw [HB] at HC
  unfold finishBirth compiledProgram parentCommands
  exact HC

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
