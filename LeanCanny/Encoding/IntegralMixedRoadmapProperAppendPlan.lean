/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendCodes
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendParentColumns
public import LeanCanny.Algebra.IntegralMixedPrefixProgramTransport
public import LeanCanny.Encoding.IntegralMixedMarkedConstructedPrefix
public import LeanCanny.Encoding.IntegralMixedMarkedSeedTailVertex
/-! # The fixed canonical proper level executes in its actual prepared-root plan -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
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
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "good"=>endpoints_good hn ht ha hR0 old hv hd left right R
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "j"=>start hn ht ha hR0 old
local notation "hj"=>prepared_start_fit hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side good
local notation "newCs"=>parentCommands hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "newX"=>parentState hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side good
local notation "startX"=>IntegralMixedMarkedConstructedPrefix.state hn ht ha hR0 r j hj

noncomputable local instance :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  preparedRoot parentCommands parentState IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth

private theorem reframe_snapshot_congr {a S B :ℕ} {V W :SpatialSource a}
    (initial :State V S B 0 (Fin 0))
    (hW :PurePowerReductionBounds.dimension (a+1) W.degree≤2^B)
    (cs ds :List (Instruction a B)) (hc :cs.length≤S+1) (hd :ds.length≤S+1) (hcs :cs=ds):
    IntegralMixedPrefixSnapshot.ofState (reframe (run initial cs hc) W hW)=
      IntegralMixedPrefixSnapshot.ofState (reframe (run initial ds hd) W hW):=by
  subst ds
  rfl

theorem parent_commands_start :newCs=IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 r j hj:=by
  have H:=IntegralMixedCausalPrefixCongruence.commands_prefix (initial P PLAN r)
    (IntegralMixedMarkedPrefixRecords.records hn ht ha hR0 r)
    (IntegralMixedMarkedPrefixRecords.room hn ht ha hR0 r) (defaultInstruction P PLAN r) (number n r+8+j)
    (by have HJ:=hj;rw [IntegralMixedMarkedPrefixRecords.length];omega)
  rw [←IntegralMixedMarkedPrefixRecords.rules hn ht ha hR0 r] at H
  have HNew :newCs=paddedPast (defaultInstruction P PLAN r) ((PLAN).rules r) (number n r+8+j):=by
    unfold parentCommands
    rw [begin_eq_start hn ht ha hR0 old R.leftSpec R.rightSpec side]
  exact HNew.trans (by
    convert H using 1; rfl)

theorem constructed_parent_snapshot :IntegralMixedPrefixSnapshot.ofState newX=
    IntegralMixedPrefixSnapshot.ofState startX:=by
  unfold parentState IntegralMixedMarkedConstructedPrefix.state IntegralMixedMarkedRecordContinuation.start
    IntegralMixedCausalUnitContinuation.start
  exact reframe_snapshot_congr _ _ _ _ _ _ (parent_commands_start hn ht ha hR0 old hv hd left right R side)

noncomputable def canonicalStartSnapshot:=IntegralMixedPrefixSnapshot.ofState x
noncomputable def actualStartSnapshot:=IntegralMixedPrefixSnapshot.ofState startX

theorem start_snapshot_eq :actualStartSnapshot hn ht ha hR0 old hv hd left right R side=
    canonicalStartSnapshot hn ht ha hR0 old hv hd:=
  (constructed_parent_snapshot hn ht ha hR0 old hv hd left right R side).symm.trans
    (parent_snapshot_eq hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side good)

noncomputable def localProgram :List (IntegralMixedFullHistoryScript.Command (Q r) ((P).width r)):=
  (canonicalStartSnapshot hn ht ha hR0 old hv hd).castProgram
    (start_snapshot_eq hn ht ha hR0 old hv hd left right R side).symm (R.levelCommands hk g hg side)

theorem local_program_length :(localProgram hn ht ha hR0 old hv hd left right R side).length=
    (R.levelCommands hk g hg side).length:=
  IntegralMixedPrefixSnapshot.Data.castProgram_length _ _

theorem local_program_heq :HEq (localProgram hn ht ha hR0 old hv hd left right R side)
    (R.levelCommands hk g hg side):=IntegralMixedPrefixSnapshot.Data.castProgram_heq _ _

theorem level_code_command_count :(R.levelCodes hk g hg side).length=(R.levelCommands hk g hg side).length:=by
  rw [R.levelCodes_length,R.levelCommands_length]



theorem local_program_room :
    (IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 r j hj).length+
      (localProgram hn ht ha hR0 old hv hd left right R side).length≤(P).cap r+1+1:=by
  have HF:=local_code_fit hn ht ha hR0 old hv hd left right R side
  have HB:=IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 r
    (number n r+8+j+(R.levelCodes hk g hg side).length) (by omega)
  rw [IntegralMixedMarkedRecordContinuation.oldCommands_length hn ht ha hR0 r j hj,
    local_program_length hn ht ha hR0 old hv hd left right R side,←level_code_command_count hn ht ha hR0 old hv hd left right R side]
  omega

theorem canonical_program_room :(oldCs).length+(R.levelCommands hk g hg side).length≤(P).cap c+1+1:=by
  have HR:=local_program_room hn ht ha hR0 old hv hd left right R side
  exact (IntegralMixedPrefixSnapshot.Data.castProgram_room
    (start_snapshot_eq hn ht ha hR0 old hv hd left right R side).symm (R.levelCommands hk g hg side)).mpr HR

noncomputable local instance :Fintype (canonicalStartSnapshot hn ht ha hR0 old hv hd).index:=by
  change Fintype (Index (Fin 0) oldCs)
  exact indexFintype (Fin 0) oldCs

noncomputable local instance :Fintype (actualStartSnapshot hn ht ha hR0 old hv hd left right R side).index:=by
  change Fintype (Index (Fin 0) (IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 r j hj))
  exact indexFintype (Fin 0) _

attribute [local irreducible] IntegralMixedOptionalEndpoints.Decodes
  IntegralMixedFullHistoryScript.continueRun IntegralMixedPrefixSnapshot.Data.castProgram
  NativePair.levelCommands NativePair.levelCodes

theorem local_decodes :Decodes startX (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha r)
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r)
    (localProgram hn ht ha hR0 old hv hd left right R side)
    (local_program_room hn ht ha hR0 old hv hd left right R side) (R.levelCodes hk g hg side):=by
  have HD:=R.level_decodes hk g hg side (canonical_program_room hn ht ha hR0 old hv hd left right R side)
  have HC:=@IntegralMixedPrefixSnapshot.Data.decodes_cast
    (canonicalStartSnapshot hn ht ha hR0 old hv hd)
    (actualStartSnapshot hn ht ha hR0 old hv hd left right R side) inferInstance inferInstance
    (start_snapshot_eq hn ht ha hR0 old hv hd left right R side).symm
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha c)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha r)
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c)
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r)
    (R.levelCommands hk g hg side) (canonical_program_room hn ht ha hR0 old hv hd left right R side)
    (local_program_room hn ht ha hR0 old hv hd left right R side) (R.levelCodes hk g hg side)
  have HR:=HC.mp HD
  convert HR using 1 <;> rfl

theorem local_run_heq :HEq
    (IntegralMixedFullHistoryScript.continueRun x (R.levelCommands hk g hg side)
      (canonical_program_room hn ht ha hR0 old hv hd left right R side))
    (IntegralMixedFullHistoryScript.continueRun startX (localProgram hn ht ha hR0 old hv hd left right R side)
      (local_program_room hn ht ha hR0 old hv hd left right R side)):=
  IntegralMixedPrefixSnapshot.Data.continueRun_cast
    (start_snapshot_eq hn ht ha hR0 old hv hd left right R side).symm (R.levelCommands hk g hg side)
    (canonical_program_room hn ht ha hR0 old hv hd left right R side)
    (local_program_room hn ht ha hR0 old hv hd left right R side)

noncomputable def compiledProgram :List (Instruction ((P).ambient r) ((P).width r)):=
  List.append ((localProgram hn ht ha hR0 old hv hd left right R side).map
    (IntegralMixedFramedFixedContinuation.wrap (Q r)
      (IntegralMixedStaticRecordPrefix.cap (Q r) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r)))) newCs

noncomputable def canonicalCompiledProgram :List (Instruction ((P).ambient c) ((P).width c)):=
  List.append ((R.levelCommands hk g hg side).map (IntegralMixedFramedFixedContinuation.wrap (Q c)
    (IntegralMixedStaticRecordPrefix.cap (Q c) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c)))) oldCs

theorem compiled_program_heq :HEq (compiledProgram hn ht ha hR0 old hv hd left right R side)
    (canonicalCompiledProgram hn ht ha hR0 old hv hd left right R side):=by
  have H:=IntegralMixedPrefixSnapshot.Data.wrappedAppend_cast
    (start_snapshot_eq hn ht ha hR0 old hv hd left right R side).symm
    (IntegralMixedStaticRecordPrefix.cap (Q c) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c))
    (IntegralMixedStaticRecordPrefix.cap (Q r) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r))
    (R.levelCommands hk g hg side) oldCs newCs
    (parent_commands_heq hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side good).symm
  convert H.symm using 1 <;> rfl

noncomputable def finishBirth:=beginBirth hn ht ha hR0 old+(R.levelCodes hk g hg side).length

theorem local_prefix_commands :paddedPast (defaultInstruction P PLAN r) ((PLAN).rules r)
    (finishBirth hn ht ha hR0 old hv hd left right R side)=compiledProgram hn ht ha hR0 old hv hd left right R side:=by
  have HC:=IntegralMixedMarkedConstructedPrefix.compiled_commands hn ht ha hR0 r j hj
    (R.levelCodes hk g hg side) (local_code_fit hn ht ha hR0 old hv hd left right R side)
    (local_code_at hn ht ha hR0 old hv hd left right R side)
    (localProgram hn ht ha hR0 old hv hd left right R side)
    (local_program_room hn ht ha hR0 old hv hd left right R side)
    (local_decodes hn ht ha hR0 old hv hd left right R side)
  rw [←begin_eq_start hn ht ha hR0 old R.leftSpec R.rightSpec side] at HC
  refine HC.trans ?_
  unfold compiledProgram
  rw [parent_commands_start hn ht ha hR0 old hv hd left right R side]
  rfl

noncomputable def meaningfulCodes:=IntegralMixedRoadmapChain.meaningfulCodes D
  (payload D old R.leftSpec R.rightSpec side)
noncomputable def seedTailCount:=IntegralMixedRoadmapChain.paddingCount D
  (payload D old R.leftSpec R.rightSpec side)+1

theorem prepared_records_tail :IntegralMixedCausalRecordPlanBits.records r=WordList.encode
    (meaningfulCodes hn ht ha hR0 old hv hd left right R side++
      List.replicate (seedTailCount hn ht ha hR0 old hv hd left right R side)
        (IntegralMixedChronologicalFrameCode.code ((P).ambient r) [] 0 0)):=by
  have HC:=pair_checked hn ht ha hR0 old hv hd left right R side []
  have HP :IntegralMixedRoadmapChain.probe (payload D old R.leftSpec R.rightSpec side)=
      IntegralMixedRoadmapChain.seedCode D:=by
    unfold payload
    exact IntegralMixedRoadmapChain.append_seed_probe _ _ _ _ _
  have HT:=IntegralMixedRoadmapChain.raw_seed_tail HC HP
  rw [prepared_dimension hn ht ha hR0 old R.leftSpec R.rightSpec side]
  simpa only [IntegralMixedCausalRecordPlanBits.records,preparedRoot,IntegralMixedRoadmapAtomic.root,
    payload_packet,pairFst_pair,pairSnd_pair,meaningfulCodes,seedTailCount,IntegralMixedRoadmapChain.seedCode] using HT

theorem meaningful_codes_birth :number n r+8+(meaningfulCodes hn ht ha hR0 old hv hd left right R side).length=
    finishBirth hn ht ha hR0 old hv hd left right R side:=by
  rw [meaningfulCodes,IntegralMixedRoadmapChain.meaningfulCodes_length]
  have HD :IntegralMixedRoadmapChain.depth (payload D old R.leftSpec R.rightSpec side)=
      IntegralMixedRoadmapAtomic.depth old+1:=by
    simp only [payload,IntegralMixedRoadmapChain.append_depth,IntegralMixedRoadmapAtomic.depth]
  rw [HD,IntegralMixedRoadmapChain.rawStart_succ,
    pair_start hn ht ha hR0 old hv hd left right R side,pair_block_count hn ht ha hR0 old hv hd left right R side]
  have HB:=begin_eq_start hn ht ha hR0 old R.leftSpec R.rightSpec side
  unfold finishBirth
  omega

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

theorem full_commands :(PLAN).rules r=
    List.replicate (seedTailCount hn ht ha hR0 old hv hd left right R side) (tailInstruction hn ht ha hR0 r)++
      compiledProgram hn ht ha hR0 old hv hd left right R side:=by
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
    (meaningfulCodes hn ht ha hR0 old hv hd left right R side)
    (seedTailCount hn ht ha hR0 old hv hd left right R side)
    (prepared_records_tail hn ht ha hR0 old hv hd left right R side)
  change (IntegralMixedMarkedReservedCutView.plan hn ht ha hR0).rules r=
    List.replicate (seedTailCount hn ht ha hR0 old hv hd left right R side) (tailInstruction hn ht ha hR0 r)++
      paddedPast (defaultInstruction P (IntegralMixedMarkedReservedCutView.plan hn ht ha hR0) r)
        ((IntegralMixedMarkedReservedCutView.plan hn ht ha hR0).rules r)
        (number n r+8+(meaningfulCodes hn ht ha hR0 old hv hd left right R side).length) at HR
  rw [IntegralMixedMarkedReservedCutView.plan_eq] at HR
  have HP :(IntegralMixedMarkedReservedParent.bank hn ht ha hR0).plan=PLAN:=rfl
  rw [HP,meaningful_codes_birth hn ht ha hR0 old hv hd left right R side,
    local_prefix_commands hn ht ha hR0 old hv hd left right R side] at HR
  exact HR

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
