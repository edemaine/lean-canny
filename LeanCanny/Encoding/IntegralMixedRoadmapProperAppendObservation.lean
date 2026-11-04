/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPlan
public import LeanCanny.Algebra.IntegralMixedFramedRunObservationCongruence
/-! # The exact new program retains the entire constructed natural observation -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "newCs"=>compiledProgram hn ht ha hR0 old hv hd left right R side
local notation "oldCs"=>canonicalCompiledProgram hn ht ha hR0 old hv hd left right R side
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank preparedRoot
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedRoadmapRetainedAppend.preparedRoot IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedAuxiliaryMarkedIntegerPlan.degree IntegralMixedAuxiliaryMarkedIntegerSource.source
  IntegralMixedAuxiliaryMarkedIntegerPlan.spatial IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedExceptionalBounds.auxiliaryCap

theorem compiled_program_room :(newCs).length≤(P).cap r+1+1:=by
  have H:=local_program_room hn ht ha hR0 old hv hd left right R side
  rw [←parent_commands_start hn ht ha hR0 old hv hd left right R side] at H
  unfold compiledProgram
  change (_++_ :List (Instruction ((P).ambient r) ((P).width r))).length≤_
  rw [List.length_append,List.length_map]
  omega

theorem canonical_compiled_room :(oldCs).length≤(P).cap c+1+1:=by
  have H:=canonical_program_room hn ht ha hR0 old hv hd left right R side
  unfold canonicalCompiledProgram
  change (_++_ :List (Instruction ((P).ambient c) ((P).width c))).length≤_
  rw [List.length_append,List.length_map]
  omega

noncomputable def compiledObservation :=IntegralMixedFramedRunObservation.ofCommands
  (initial P PLAN r) newCs (compiled_program_room hn ht ha hR0 old hv hd left right R side)

noncomputable def canonicalObservation :=IntegralMixedFramedRunObservation.ofCommands
  (initial P PLAN c) oldCs (canonical_compiled_room hn ht ha hR0 old hv hd left right R side)

theorem compiled_observation_eq :compiledObservation hn ht ha hR0 old hv hd left right R side=
    canonicalObservation hn ht ha hR0 old hv hd left right R side:=by
  have HC:IntegralMixedAuxiliaryMarkedIntegerSource.candidate r=
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate c:=
    (prepared_candidate hn ht ha hR0 old R.leftSpec R.rightSpec side).trans
      (IntegralMixedRoadmapRetainedAppend.prepared_candidate hn ht ha hR0 old e).symm
  have HCount:IntegralMixedCausalRecordPlanBits.count r=IntegralMixedCausalRecordPlanBits.count c:=
    (prepared_count hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side
      (endpoints_good hn ht ha hR0 old hv hd left right R)).trans
      (IntegralMixedRoadmapRetainedAppend.prepared_count hn ht ha hR0 old hv hd e
        (IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old)).symm
  exact IntegralMixedFramedRunObservation.ofCommands_heq (initial P PLAN r) (initial P PLAN c)
    newCs oldCs (compiled_program_room hn ht ha hR0 old hv hd left right R side)
    (canonical_compiled_room hn ht ha hR0 old hv hd left right R side)
    (IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 r c HC)
    (congrArg (·+1) (IntegralMixedMarkedPrefixParameters.cap hn ht ha hR0 r c HC HCount))
    (IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 r c HC)
    (IntegralMixedMarkedPrefixRecords.source_heq (n:=n) (t:=t) (R0:=R0) r c HC)
    (IntegralMixedMarkedPrefixRecords.initial_heq hn ht ha hR0 r c HC HCount)
    (compiled_program_heq hn ht ha hR0 old hv hd left right R side)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
