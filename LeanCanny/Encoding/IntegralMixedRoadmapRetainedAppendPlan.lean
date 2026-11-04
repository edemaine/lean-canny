/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendCodes
public import LeanCanny.Geometry.IntegralMixedPointCompanionDecoded
public import LeanCanny.Encoding.IntegralMixedMarkedSeedTailVertex
/-! # The actual retained append executes the literal two-block program

Every decoder equation is derived from its typed critical record. The
interpreter identity concerns the actual prepared root, not an old word.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedPointCompanion IntegralMixedFrozenFrame
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" r=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (e :ℕ) (he :e<IntegralMixedRoadmapAtomic.endBirth
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old)
local notation "r"=>preparedRoot hn ht ha hR0 old e
local notation "older"=>parentCommands hn ht ha hR0 old hv hd e he
local notation "d"=>parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "a"=>endpointLabel hn ht ha hR0 old hv hd e he
local notation "F"=>IntegralMixedChronologicalMidpoint.frame d hk a a
local notation "g"=>midpointObjective hn ht ha hR0 old hv hd e he
local notation "js"=>midpointSelections hn ht ha hR0 old hv hd e he
local notation "dc"=>childDescriptor hn ht ha hR0 old hv hd e he
local notation "gc"=>childObjective hn ht ha hR0 old hv hd e he
local notation "cs"=>childSelections hn ht ha hR0 old hv hd e he
local notation "positive"=>IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha r
local notation "cap"=>IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r

theorem parent_state_start :parentState hn ht ha hR0 old hv hd e he=
    IntegralMixedMarkedConstructedPrefix.state hn ht ha hR0 r (start hn ht ha hR0 old)
      (prefix_fit hn ht ha hR0 old hv hd e he):=by
  unfold parentState IntegralMixedMarkedConstructedPrefix.state IntegralMixedMarkedRecordContinuation.start
    IntegralMixedCausalUnitContinuation.start parentCommands IntegralMixedMarkedRecordContinuation.oldCommands
  rfl

noncomputable def localProgram :List (IntegralMixedFullHistoryScript.Command (Q r) ((P).width r)):=
  commands (dc).frame.frozen (fun _=>false) (fun i=>.single ((dc).atom i)) gc cs++
    midpointCommands hn ht ha hR0 old hv hd e he

theorem local_program_room :(older).length+(localProgram hn ht ha hR0 old hv hd e he).length≤(P).cap r+1+1:=by
  have HR:=child_room hn ht ha hR0 old hv hd e he
  simp only [localProgram,List.length_append,midpointCommands,commands_length]
  omega

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap preparedRoot parentCommands parentDescriptor
  parentState midpointObjective childDescriptor childObjective IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth IntegralMixedRoadmapAtomic.frozen
  IntegralMixedFramedHistoryScript.Index

theorem local_decodes :IntegralMixedOptionalEndpoints.Decodes (parentState hn ht ha hR0 old hv hd e he)
    positive cap (localProgram hn ht ha hR0 old hv hd e he)
      (local_program_room hn ht ha hR0 old hv hd e he) (localCodes hn ht ha hR0 old hv hd e he):=by
  have HM:=IntegralMixedPointCompanion.decodes_append («P»:=Q r) (S:=(P).cap r+1) (B:=(P).width r) (parentState hn ht ha hR0 old hv hd e he)
    (F).frozen (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk))
    (IntegralMixedChronologicalMidpoint.rows d hk a a) g positive cap []
    (by simpa only [List.length_nil,Nat.add_zero] using parent_room hn ht ha hR0 old hv hd e he)
    [] rfl (Nat.add_zero _).symm js
    (by simpa only [List.append_nil,commands_length] using midpoint_room hn ht ha hR0 old hv hd e he)
  simp only [List.append_nil] at HM
  have HM' :IntegralMixedOptionalEndpoints.Decodes (parentState hn ht ha hR0 old hv hd e he)
      positive cap (midpointCommands hn ht ha hR0 old hv hd e he)
      (by simpa only [midpointCommands,commands_length] using midpoint_room hn ht ha hR0 old hv hd e he)
      (midpointCodes hn ht ha hR0 old hv hd e he):=HM
  have HC:=IntegralMixedPointCompanion.decodes_append («P»:=Q r) (S:=(P).cap r+1) (B:=(P).width r) (parentState hn ht ha hR0 old hv hd e he)
    (dc).frame.frozen (fun _=>false) (fun i=>.single ((dc).atom i)) gc positive cap
    (midpointCommands hn ht ha hR0 old hv hd e he) _ (midpointCodes hn ht ha hR0 old hv hd e he) HM'
    (by simp only [midpointCommands,commands_length]) cs
    (by
      rw [List.length_append,commands_length]
      have HM :(midpointCommands hn ht ha hR0 old hv hd e he).length=(js).length:=by
        rw [midpointCommands,commands_length]
      rw [HM]
      have HR:=child_room hn ht ha hR0 old hv hd e he
      omega)
  exact HC

theorem local_finish_index :number n r+8+start hn ht ha hR0 old+
    (localCodes hn ht ha hR0 old hv hd e he).length=finishBirth hn ht ha hR0 old e:=by
  rw [local_codes_length,finish_eq]
  have HB :(older).length=number n r+8+start hn ht ha hR0 old:=by
    rw [parentCommands,IntegralMixedMarkedRecordContinuation.oldCommands_length]
  have HE:=parent_length hn ht ha hR0 old hv hd e he
  change (older).length=beginBirth hn ht ha hR0 old at HE
  omega

theorem local_code_fit :start hn ht ha hR0 old+(localCodes hn ht ha hR0 old hv hd e he).length≤
    IntegralMixedCausalRecordPlanBits.count r:=by
  have HF:=finish_le_full hn ht ha hR0 old hv hd e he
  rw [←local_finish_index hn ht ha hR0 old hv hd e he] at HF
  change _≤number n r+8+IntegralMixedCausalRecordPlanBits.count r at HF
  omega

attribute [local irreducible] localProgram localCodes midpointCommands
  midpointCodes childCodes start IntegralMixedCausalRecordPlanBits.count
  IntegralMixedMarkedConstructedPrefix.state IntegralMixedMarkedRecordContinuation.oldCommands

noncomputable def compiledProgram :List (Instruction ((P).ambient r) ((P).width r)):=
  List.append ((localProgram hn ht ha hR0 old hv hd e he).map (IntegralMixedFramedFixedContinuation.wrap (Q r)
    (IntegralMixedStaticRecordPrefix.cap (Q r) cap))) older

attribute [local semireducible] parentCommands

theorem local_prefix_commands :paddedPast (defaultInstruction P D r) ((D).rules r)
    (finishBirth hn ht ha hR0 old e)=compiledProgram hn ht ha hR0 old hv hd e he:=by
  have roomActual :(IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 r
      (start hn ht ha hR0 old) (prefix_fit hn ht ha hR0 old hv hd e he)).length+
      (localProgram hn ht ha hR0 old hv hd e he).length≤(P).cap r+1+1:=by
    simpa only [parentCommands] using local_program_room hn ht ha hR0 old hv hd e he
  have HD:=(IntegralMixedOptionalEndpoints.Decodes.congr_start
    (parentState hn ht ha hR0 old hv hd e he)
    (IntegralMixedMarkedConstructedPrefix.state hn ht ha hR0 r (start hn ht ha hR0 old)
      (prefix_fit hn ht ha hR0 old hv hd e he)) rfl rfl
    (heq_of_eq (parent_state_start hn ht ha hR0 old hv hd e he)) positive cap
    (localProgram hn ht ha hR0 old hv hd e he)
    (local_program_room hn ht ha hR0 old hv hd e he) roomActual
    (localCodes hn ht ha hR0 old hv hd e he)).mp (local_decodes hn ht ha hR0 old hv hd e he)
  have HC:=IntegralMixedMarkedConstructedPrefix.compiled_commands hn ht ha hR0 r
    (start hn ht ha hR0 old) (prefix_fit hn ht ha hR0 old hv hd e he)
    (localCodes hn ht ha hR0 old hv hd e he) (local_code_fit hn ht ha hR0 old hv hd e he)
    (local_code_at hn ht ha hR0 old hv hd e he) (localProgram hn ht ha hR0 old hv hd e he)
    roomActual HD
  rw [local_finish_index] at HC
  refine HC.trans ?_
  unfold compiledProgram parentCommands
  rfl

attribute [local semireducible] IntegralMixedMarkedReservedParent.bank

noncomputable def tailInstruction (root :List Bool):Instruction ((P).ambient root) ((P).width root):=
  IntegralMixedSourceIntegerPaddingPrefix.seedInstruction P
    (IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.positive hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.degree hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.scalar_cap hn ht ha hR0) root

theorem tail_instruction_command (root :List Bool):
    (tailInstruction hn ht ha hR0 root).command=
      .critical (IntegralMixedCanonicalPaddingSeed.rule ((P).ambient root)):=rfl

theorem full_commands :(D).rules r=
    List.replicate (seedTailCount hn ht ha hR0 old e) (tailInstruction hn ht ha hR0 r)++
      compiledProgram hn ht ha hR0 old hv hd e he:=by
  have HR:=IntegralMixedSourceIntegerSeedTail.full_seed_tail P
    (IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.positive hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.degree hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.scalar_cap hn ht ha hR0) (fun root=>number n root+8)
    (IntegralMixedMarkedReservedCutView.integerSource hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.integer_nonzero hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.integer_cap hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.room hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.data hn ht ha hR0) r []
    (retainedCodes hn ht ha hR0 old e) (seedTailCount hn ht ha hR0 old e)
    (prepared_records_tail hn ht ha hR0 old hv hd e he)
  change (IntegralMixedMarkedReservedCutView.plan hn ht ha hR0).rules r=
    List.replicate (seedTailCount hn ht ha hR0 old e) (tailInstruction hn ht ha hR0 r)++
      paddedPast (defaultInstruction P (IntegralMixedMarkedReservedCutView.plan hn ht ha hR0) r)
        ((IntegralMixedMarkedReservedCutView.plan hn ht ha hR0).rules r)
        (number n r+8+(retainedCodes hn ht ha hR0 old e).length) at HR
  rw [IntegralMixedMarkedReservedCutView.plan_eq] at HR
  have HP : (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).plan=D:=rfl
  rw [HP,retained_codes_birth,local_prefix_commands] at HR
  exact HR

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
