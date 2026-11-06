/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendEndpointSnapshot
/-! # The actual MID prefix includes all and only the chosen endpoint commands -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalEndpoint
open IntegralMixedFramedHistoryFamilyBits (defaultInstruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem drop_newer {α : Type} (newer older : List α) :
    (newer++older).drop newer.length=older := by
  rw [List.drop_append,List.drop_length,List.nil_append,Nat.sub_self,List.drop_zero]

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e
local notation "oldCs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he
local notation "g" => FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he
local notation "hg" => FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd e he
noncomputable local instance providerProperEndpointBoundaryFintype : Fintype (Index (Fin 0) oldCs) :=
  indexFintype (Fin 0) oldCs
variable (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side
local notation "wrapC" => canonicalEndpointWrap old
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  preparedRoot FormulaSignSlotRadialProviderRetainedAppend.preparedRoot
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.depth

/-- This includes the zero-fresh-endpoint case. -/
theorem midpoint_prefix_commands :
    HEq (paddedPast (defaultInstruction P D r) ((D).rules r) (midpointBirth old hv hd left right R))
      (R.result.commands.map wrapC++oldCs) := by
  let newer := R.levelChildCommands hk g hg side++[.critical (R.levelEndpointData hk g hg side).rule]++
    R.levelMidpointCommands hk g hg++[.critical (R.levelMidpointData hk g hg).rule]
  have HL : R.levelCommands hk g hg side=newer++R.result.commands := by
    simp only [NativePair.levelCommands,newer,List.append_assoc]
  have HS : canonicalCompiledProgram old hv hd left right R side=
      newer.map wrapC++(R.result.commands.map wrapC++oldCs) := by
    change (R.levelCommands hk g hg side).map wrapC++oldCs=_
    rw [HL,List.map_append,List.append_assoc]
  have HLen := congrArg List.length HL
  simp only [List.length_append] at HLen
  have HCode := level_code_command_count old hv hd left right R side
  have HDiff : finishBirth old hv hd left right R side-midpointBirth old hv hd left right R=newer.length := by
    unfold finishBirth midpointBirth
    omega
  have HDrop := paddedPast_drop (defaultInstruction P D r) ((D).rules r)
    (finishBirth old hv hd left right R side) (midpointBirth old hv hd left right R)
    (midpoint_lt_finish old hv hd left right R side).le
  rw [local_prefix_commands old hv hd left right R side,HDiff] at HDrop
  have HP : FormulaSignSlotRadialProviderRecordPlan.providerContext r=
      FormulaSignSlotRadialProviderRecordPlan.providerContext c :=
    (prepared_provider old R.leftSpec R.rightSpec side).trans
      (FormulaSignSlotRadialProviderRetainedAppend.prepared_provider old e).symm
  have HC := IntegralMixedPrefixSnapshot.list_drop_heq
    (compiledProgram old hv hd left right R side) (canonicalCompiledProgram old hv hd left right R side)
    (FormulaSignSlotRadialProviderRecordPrefix.ambient r c HP)
    (FormulaSignSlotRadialProviderRecordPrefix.width r c HP)
    (compiled_program_heq old hv hd left right R side) newer.length
  rw [HDrop] at HC
  have HRest : (canonicalCompiledProgram old hv hd left right R side).drop newer.length=
      R.result.commands.map wrapC++oldCs := by
    rw [HS]
    simpa only [List.length_map] using drop_newer (newer.map wrapC) (R.result.commands.map wrapC++oldCs)
  exact HC.trans (heq_of_eq HRest)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
