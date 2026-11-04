/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPlan
public import LeanCanny.Algebra.IntegralMixedPrefixProgramPartial
public import LeanCanny.Geometry.IntegralMixedGuardedProgramCutAt
/-! # Every chosen endpoint command has its literal actual creating snapshot -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number candidate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem endpoint_commands_snapshot_congr {a S B :ℕ} {V :SpatialSource a}
    (initial :State V S B 0 (Fin 0)) (cs ds :List (Instruction a B))
    (hc :cs.length≤S+1) (hd :ds.length≤S+1) (he :cs=ds) :
    IntegralMixedPrefixSnapshot.ofCommands initial cs hc=
      IntegralMixedPrefixSnapshot.ofCommands initial ds hd:=by
  subst ds
  rfl

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side

noncomputable local instance :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  preparedRoot IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth

noncomputable def endpointBirth (i :ℕ):=beginBirth hn ht ha hR0 old+R.result.commands.length-1-i
noncomputable def endpointRawIndex (i :ℕ):=start hn ht ha hR0 old+R.result.commands.length-1-i

private noncomputable def endpointNewer:=
  R.levelChildCommands hk g hg side++[.critical (R.levelEndpointData hk g hg side).rule]++
    R.levelMidpointCommands hk g hg++[.critical (R.levelMidpointData hk g hg).rule]

private theorem endpoint_level_split :R.levelCommands hk g hg side=
    endpointNewer hn ht ha hR0 old hv hd left right R side++R.result.commands:=by
  simp only [NativePair.levelCommands,endpointNewer,List.append_assoc]

private theorem endpoint_parent_birth :(oldCs).length=beginBirth hn ht ha hR0 old:=
  IntegralMixedRoadmapRetainedAppend.parent_length hn ht ha hR0 old hv hd e he

theorem endpoint_birth_eq (i :ℕ) (hi :i<R.result.commands.length) :
    endpointBirth hn ht ha hR0 old hv hd left right R i=
      number n r+8+endpointRawIndex hn ht ha hR0 old hv hd left right R i:=by
  have HB:=begin_eq_start hn ht ha hR0 old R.leftSpec R.rightSpec side
  unfold endpointBirth endpointRawIndex
  omega

theorem endpoint_raw_fit (i :ℕ) :
    endpointRawIndex hn ht ha hR0 old hv hd left right R i≤IntegralMixedCausalRecordPlanBits.count r:=by
  have HF:=local_code_fit hn ht ha hR0 old hv hd left right R side
  have HL:=R.levelCodes_length hk g hg side
  unfold endpointRawIndex
  omega

private theorem endpoint_before_finish (i :ℕ) (hi :i<R.result.commands.length) :
    endpointBirth hn ht ha hR0 old hv hd left right R i<
      finishBirth hn ht ha hR0 old hv hd left right R side:=by
  have HL:=R.levelCodes_length hk g hg side
  unfold endpointBirth finishBirth
  omega

private theorem endpoint_candidate :candidate r=candidate c:=
  (prepared_candidate hn ht ha hR0 old R.leftSpec R.rightSpec side).trans
    (IntegralMixedRoadmapRetainedAppend.prepared_candidate hn ht ha hR0 old e).symm

private theorem endpoint_count :IntegralMixedCausalRecordPlanBits.count r=
    IntegralMixedCausalRecordPlanBits.count c:=
  (prepared_count hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side
    (endpoints_good hn ht ha hR0 old hv hd left right R)).trans
    (IntegralMixedRoadmapRetainedAppend.prepared_count hn ht ha hR0 old hv hd e he).symm

noncomputable def canonicalEndpointWrap (cmd :IntegralMixedFullHistoryScript.Command (Q c) ((P).width c)) :
    Instruction ((P).ambient c) ((P).width c):=
  IntegralMixedFramedFixedContinuation.wrap (Q c)
    (IntegralMixedStaticRecordPrefix.cap (Q c) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c)) cmd
local notation "wrapC"=>canonicalEndpointWrap hn ht ha hR0 old

private theorem endpoint_map_drop {α β :Type} (f :α→β) (cs :List α) (j :ℕ) :
    (cs.map f).drop j=(cs.drop j).map f:=by
  induction cs generalizing j with
  | nil=>simp
  | cons a cs ih=>cases j with
    | zero=>rfl
    | succ j=>exact ih j

private theorem canonical_endpoint_split :canonicalCompiledProgram hn ht ha hR0 old hv hd left right R side=
    (endpointNewer hn ht ha hR0 old hv hd left right R side).map wrapC++
    R.result.commands.map wrapC++oldCs:=by
  unfold canonicalCompiledProgram
  rw [endpoint_level_split hn ht ha hR0 old hv hd left right R side,List.map_append]
  rfl

noncomputable def endpointPartialCommands (i :ℕ) :List (Instruction ((P).ambient c) ((P).width c)):=
  (R.result.commands.drop (i+1)).map wrapC++oldCs

theorem endpoint_prefix_commands (i :ℕ) (hi :i<R.result.commands.length) :
    HEq (paddedPast (defaultInstruction P PLAN r) ((PLAN).rules r)
      (endpointBirth hn ht ha hR0 old hv hd left right R i))
      (endpointPartialCommands hn ht ha hR0 old hv hd left right R i):=by
  let skip:=(endpointNewer hn ht ha hR0 old hv hd left right R side).length+(i+1)
  have HB:=endpoint_before_finish hn ht ha hR0 old hv hd left right R side i hi
  have HD:=paddedPast_drop (defaultInstruction P PLAN r) ((PLAN).rules r)
    (finishBirth hn ht ha hR0 old hv hd left right R side)
    (endpointBirth hn ht ha hR0 old hv hd left right R i) HB.le
  rw [local_prefix_commands hn ht ha hR0 old hv hd left right R side] at HD
  have HS:finishBirth hn ht ha hR0 old hv hd left right R side-
      endpointBirth hn ht ha hR0 old hv hd left right R i=skip:=by
    have HL:=congrArg List.length (endpoint_level_split hn ht ha hR0 old hv hd left right R side)
    simp only [List.length_append] at HL
    have HC:=level_code_command_count hn ht ha hR0 old hv hd left right R side
    unfold finishBirth endpointBirth skip
    omega
  rw [HS] at HD
  have HC:=IntegralMixedPrefixSnapshot.list_drop_heq
    (compiledProgram hn ht ha hR0 old hv hd left right R side)
    (canonicalCompiledProgram hn ht ha hR0 old hv hd left right R side)
    (IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 r c
      (endpoint_candidate hn ht ha hR0 old hv hd left right R side))
    (IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 r c
      (endpoint_candidate hn ht ha hR0 old hv hd left right R side))
    (compiled_program_heq hn ht ha hR0 old hv hd left right R side) skip
  rw [HD,canonical_endpoint_split hn ht ha hR0 old hv hd left right R side] at HC
  have HE:=IntegralMixedPrefixSnapshot.partial_drop
    ((endpointNewer hn ht ha hR0 old hv hd left right R side).map wrapC)
    (R.result.commands.map wrapC)
    oldCs i (by simpa only [List.length_map] using hi)
  simp only [List.length_map,endpoint_map_drop] at HE
  change _=endpointPartialCommands hn ht ha hR0 old hv hd left right R i at HE
  dsimp only [skip] at HC
  rw [HE] at HC
  exact HC

private theorem endpoint_partial_room (i :ℕ) :
    (endpointPartialCommands hn ht ha hR0 old hv hd left right R i).length≤(P).cap c+1+1:=by
  have H:=cutAt_room R.result.commands R.result.room i
  change (oldCs).length+(R.result.commands.drop (i+1)).length≤_ at H
  unfold endpointPartialCommands
  rw [List.length_append,List.length_map]
  omega

theorem endpoint_snapshot (i :ℕ) (hi :i<R.result.commands.length) :
    IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 r
      (endpointRawIndex hn ht ha hR0 old hv hd left right R i)
      (endpoint_raw_fit hn ht ha hR0 old hv hd left right R side i)=
    IntegralMixedPrefixSnapshot.ofState
      (IntegralMixedFullHistoryScript.continueRun x (R.result.commands.drop (i+1))
        (cutAt_room R.result.commands R.result.room i)):=by
  have HE:=IntegralMixedPrefixSnapshot.ofCommands_heq (initial P PLAN r) (initial P PLAN c)
    (paddedPast (defaultInstruction P PLAN r) ((PLAN).rules r)
      (endpointBirth hn ht ha hR0 old hv hd left right R i))
    (endpointPartialCommands hn ht ha hR0 old hv hd left right R i)
    (by rw [paddedPast_length,endpoint_birth_eq hn ht ha hR0 old hv hd left right R side i hi]
        exact (IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 r _
          (endpoint_raw_fit hn ht ha hR0 old hv hd left right R side i)).trans (Nat.le_succ _))
    (endpoint_partial_room hn ht ha hR0 old hv hd left right R i)
    (IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 r c
      (endpoint_candidate hn ht ha hR0 old hv hd left right R side))
    (congrArg (·+1) (IntegralMixedMarkedPrefixParameters.cap hn ht ha hR0 r c
      (endpoint_candidate hn ht ha hR0 old hv hd left right R side)
      (endpoint_count hn ht ha hR0 old hv hd left right R side)))
    (IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 r c
      (endpoint_candidate hn ht ha hR0 old hv hd left right R side))
    (IntegralMixedMarkedPrefixRecords.source_heq (n:=n) (t:=t) (R0:=R0) r c
      (endpoint_candidate hn ht ha hR0 old hv hd left right R side))
    (IntegralMixedMarkedPrefixRecords.initial_heq hn ht ha hR0 r c
      (endpoint_candidate hn ht ha hR0 old hv hd left right R side)
      (endpoint_count hn ht ha hR0 old hv hd left right R side))
    (endpoint_prefix_commands hn ht ha hR0 old hv hd left right R side i hi)
  have HS:IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 r
      (endpointRawIndex hn ht ha hR0 old hv hd left right R i)
      (endpoint_raw_fit hn ht ha hR0 old hv hd left right R side i)=
      IntegralMixedPrefixSnapshot.ofCommands (initial P PLAN r)
        (paddedPast (defaultInstruction P PLAN r) ((PLAN).rules r)
          (endpointBirth hn ht ha hR0 old hv hd left right R i)) (by
            rw [paddedPast_length,endpoint_birth_eq hn ht ha hR0 old hv hd left right R side i hi]
            exact (IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 r _
              (endpoint_raw_fit hn ht ha hR0 old hv hd left right R side i)).trans (Nat.le_succ _)):=by
    unfold IntegralMixedMarkedPrefixSnapshot.snapshot
    exact endpoint_commands_snapshot_congr _ _ _ _ _
      (congrArg (paddedPast (defaultInstruction P PLAN r) ((PLAN).rules r))
        (endpoint_birth_eq hn ht ha hR0 old hv hd left right R side i hi).symm)
  refine HS.trans (HE.trans ?_)
  unfold endpointPartialCommands canonicalEndpointWrap IntegralMixedRoadmapRetainedAppend.parentState
  exact IntegralMixedPrefixSnapshot.wrapped_append _ _ _ (Q c) (initial P PLAN c)
    (IntegralMixedStaticRecordPrefix.cap (Q c) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c))
    oldCs (IntegralMixedRoadmapRetainedAppend.parent_room hn ht ha hR0 old hv hd e he)
    (R.result.commands.drop (i+1)) (cutAt_room R.result.commands R.result.room i)

theorem endpoint_birth_cap (i :ℕ) (hi :i<R.result.commands.length) :
    endpointBirth hn ht ha hR0 old hv hd left right R i≤(P).cap r+1:=by
  rw [endpoint_birth_eq hn ht ha hR0 old hv hd left right R side i hi]
  exact IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 r _
    (endpoint_raw_fit hn ht ha hR0 old hv hd left right R side i)

theorem endpoint_birth_lt_full (i :ℕ) (hi :i<R.result.commands.length) :
    endpointBirth hn ht ha hR0 old hv hd left right R i<
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n r:=by
  have HF:=local_code_fit hn ht ha hR0 old hv hd left right R side
  have HL:=R.levelCodes_length hk g hg side
  have HB:=endpoint_birth_eq hn ht ha hR0 old hv hd left right R side i hi
  unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount endpointRawIndex at *
  omega

theorem endpoint_instruction (i :ℕ) (hi :i<R.result.commands.length) :
    HEq (IntegralMixedFramedRootPullback.instructionAt P PLAN r
      (endpointBirth hn ht ha hR0 old hv hd left right R i)) (wrapC R.result.commands[i]):=by
  have HCan:=IntegralMixedPrefixSnapshot.partial_chronological
    ((endpointNewer hn ht ha hR0 old hv hd left right R side).map wrapC)
    (R.result.commands.map wrapC) oldCs i (by simpa only [List.length_map] using hi)
  simp only [List.length_map,List.getElem_map] at HCan
  have HB:=congrArg (fun b :ℕ=>b+R.result.commands.length-1-i)
    (endpoint_parent_birth hn ht ha hR0 old hv hd)
  have HCan':=(congrArg
    (chronological ((endpointNewer hn ht ha hR0 old hv hd left right R side).map wrapC++
      R.result.commands.map wrapC++oldCs)) HB).symm.trans HCan
  change chronological _ (endpointBirth hn ht ha hR0 old hv hd left right R i)=some (wrapC R.result.commands[i]) at HCan'
  rw [←canonical_endpoint_split hn ht ha hR0 old hv hd left right R side] at HCan'
  have HC:=IntegralMixedPrefixSnapshot.chronological_get_heq
    (compiledProgram hn ht ha hR0 old hv hd left right R side)
    (canonicalCompiledProgram hn ht ha hR0 old hv hd left right R side)
    (IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 r c
      (endpoint_candidate hn ht ha hR0 old hv hd left right R side))
    (IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 r c
      (endpoint_candidate hn ht ha hR0 old hv hd left right R side))
    (compiled_program_heq hn ht ha hR0 old hv hd left right R side)
    (endpointBirth hn ht ha hR0 old hv hd left right R i) (defaultInstruction P PLAN r)
    (wrapC R.result.commands[i]) HCan'
  have HA:=paddedPast_chronological (defaultInstruction P PLAN r) ((PLAN).rules r)
    (finishBirth hn ht ha hR0 old hv hd left right R side)
    (endpointBirth hn ht ha hR0 old hv hd left right R i)
    (endpoint_before_finish hn ht ha hR0 old hv hd left right R side i hi)
  rw [local_prefix_commands hn ht ha hR0 old hv hd left right R side] at HA
  have HR:(chronological (compiledProgram hn ht ha hR0 old hv hd left right R side)
      (endpointBirth hn ht ha hR0 old hv hd left right R i)).getD (defaultInstruction P PLAN r)=
      IntegralMixedFramedRootPullback.instructionAt P PLAN r
        (endpointBirth hn ht ha hR0 old hv hd left right R i):=by
    rw [HA]
    rfl
  exact (heq_of_eq HR.symm).trans HC

theorem endpoint_command (i :ℕ) (hi :i<R.result.commands.length) :
    HEq (IntegralMixedFramedRootPullback.instructionAt P PLAN r
      (endpointBirth hn ht ha hR0 old hv hd left right R i)).command R.result.commands[i]:=
  IntegralMixedPrefixSnapshot.instruction_command_heq _ _
    (IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 r c
      (endpoint_candidate hn ht ha hR0 old hv hd left right R side))
    (IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 r c
      (endpoint_candidate hn ht ha hR0 old hv hd left right R side))
    (endpoint_instruction hn ht ha hR0 old hv hd left right R side i hi)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
