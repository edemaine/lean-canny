/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPlan
public import LeanCanny.Algebra.IntegralMixedFramedRunObservationCongruence
/-! # The general provider program keeps the complete constructed observation -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
  (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "PLAN" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e
local notation "newCs" => compiledProgram old hv hd left right R side
local notation "oldCs" => canonicalCompiledProgram old hv hd left right R side
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands

theorem compiled_program_room :(newCs).length≤(P).cap r+1+1:=by
  have H:=local_program_room old hv hd left right R side
  unfold compiledProgram parentCommands
  change (_++_ :List (Instruction ((P).ambient r) ((P).width r))).length≤_
  rw [List.length_append,List.length_map]
  omega

theorem canonical_compiled_room :(oldCs).length≤(P).cap c+1+1:=by
  have H:=canonical_program_room old hv hd left right R side
  unfold canonicalCompiledProgram
  change (_++_ :List (Instruction ((P).ambient c) ((P).width c))).length≤_
  rw [List.length_append,List.length_map]
  omega

noncomputable def compiledObservation :=IntegralMixedFramedRunObservation.ofCommands
  (initial P PLAN r) newCs (compiled_program_room old hv hd left right R side)

noncomputable def canonicalObservation :=IntegralMixedFramedRunObservation.ofCommands
  (initial P PLAN c) oldCs (canonical_compiled_room old hv hd left right R side)

theorem compiled_observation_eq :compiledObservation old hv hd left right R side=
    canonicalObservation old hv hd left right R side:=by
  have HC := (prepared_provider old R.leftSpec R.rightSpec side).trans
    (FormulaSignSlotRadialProviderRetainedAppend.prepared_provider old e).symm
  have HCount := (prepared_count old hv hd R.leftSpec R.rightSpec side
    (endpoints_good old hv hd left right R)).trans
    (FormulaSignSlotRadialProviderRetainedAppend.prepared_count old hv hd e
      (FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old)).symm
  exact IntegralMixedFramedRunObservation.ofCommands_heq (initial P PLAN r) (initial P PLAN c)
    newCs oldCs (compiled_program_room old hv hd left right R side)
    (canonical_compiled_room old hv hd left right R side)
    (FormulaSignSlotRadialProviderRecordPrefix.ambient r c HC)
    (congrArg (·+1) (FormulaSignSlotRadialProviderRecordPrefix.cap r c HC HCount))
    (FormulaSignSlotRadialProviderRecordPrefix.width r c HC)
    (FormulaSignSlotRadialProviderRecordPrefix.source_heq r c HC)
    (FormulaSignSlotRadialProviderRecordPrefix.initial_heq r c HC HCount)
    (compiled_program_heq old hv hd left right R side)

attribute [local irreducible] compiledObservation canonicalObservation

theorem tuple_roots (z :ℕ→ℝ)
    (hz :(canonicalObservation old hv hd left right R side).Roots z):
    (compiledObservation old hv hd left right R side).Roots z:=
  Eq.mpr (congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.Roots z)
    (compiled_observation_eq old hv hd left right R side)) hz

theorem tuple_arity :(compiledObservation old hv hd left right R side).arity=
    (canonicalObservation old hv hd left right R side).arity:=
  congrArg IntegralMixedFramedRunObservation.Data.arity
    (compiled_observation_eq old hv hd left right R side)

theorem tuple_point (z :ℕ→ℝ) (i :ℕ):
    (compiledObservation old hv hd left right R side).point z i=
      (canonicalObservation old hv hd left right R side).point z i:=
  congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.point z i)
    (compiled_observation_eq old hv hd left right R side)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
