/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPlan
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedCriticalTail
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendParentColumns
public import LeanCanny.Algebra.IntegralMixedPrefixProgramTransport
public import LeanCanny.Encoding.IntegralMixedMarkedConstructedPrefix
public import LeanCanny.Encoding.IntegralMixedMarkedSeedTailVertex
/-! # Literal midpoint, child, and seed-tail windows of a canonical proper append -/
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

noncomputable local instance properAppendWindowsIndexFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  preparedRoot parentCommands parentState IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth

local notation "q"=>packet D old R.leftSpec R.rightSpec side []
local notation "K"=>List.length (R.orderedFree hk)

theorem capture_count :IntegralMixedRoadmapProper.captureCount
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) q=K:=by
  rw [dimension_packet]
  have HL:=R.orderedFree_length hk
  have HDIM:=IntegralMixedRoadmapRetainedAppend.prepared_dimension hn ht ha hR0 old e
  have HLEN:=IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd e he
  have HNUM :((P).ambient c)+1-((d).labels.length+1)=D-IntegralMixedRoadmapAtomic.depth old:=by omega
  have HK :K=D-IntegralMixedRoadmapAtomic.depth old:=HL.trans HNUM
  unfold IntegralMixedRoadmapProper.captureCount IntegralMixedRoadmapProper.levelIndex
  rw [depth_packet]
  omega

theorem child_free :IntegralMixedRoadmapAtomic.free
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) q=K:=by
  have HD :IntegralMixedRoadmapAtomic.depth q≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q:=by
    rw [depth_packet,dimension_packet]
    omega
  have HP :0<IntegralMixedRoadmapAtomic.depth q:=by rw [depth_packet];omega
  exact (IntegralMixedRoadmapCheckedCriticalTail.latest_layout
    (initial:=IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) HD HP).2.1.trans
      (capture_count hn ht ha hR0 old hv hd left right R side)

theorem end_birth_finish :IntegralMixedRoadmapAtomic.endBirth
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
    (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q=
      finishBirth hn ht ha hR0 old hv hd left right R side:=
  end_birth hn ht ha hR0 old hv hd left right R side []

theorem finish_midpoint :finishBirth hn ht ha hR0 old hv hd left right R side=
    IntegralMixedRoadmapProper.midBirth (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q+2+2*K:=by
  have HC :IntegralMixedRoadmapAtomic.depth q≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q:=by
    rw [depth_packet,dimension_packet]
    omega
  have HP :0<IntegralMixedRoadmapAtomic.depth q:=by rw [depth_packet];omega
  have HL:=(IntegralMixedRoadmapCheckedCriticalTail.latest_layout
    (initial:=IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) HC HP).1
  rw [end_birth_finish hn ht ha hR0 old hv hd left right R side,
    capture_count hn ht ha hR0 old hv hd left right R side] at HL
  exact HL

theorem midpoint_birth :IntegralMixedRoadmapProper.midBirth
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
    (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q=
      beginBirth hn ht ha hR0 old+R.result.commands.length:=by
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  unfold finishBirth at HF
  rw [R.levelCodes_length] at HF
  omega

theorem child_anchor :IntegralMixedRoadmapAtomic.anchor
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
    (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q=
      IntegralMixedRoadmapProper.midBirth (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
        (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q+1+K:=by
  have HC :IntegralMixedRoadmapAtomic.depth q≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q:=by
    rw [depth_packet,dimension_packet]
    omega
  have HP :0<IntegralMixedRoadmapAtomic.depth q:=by rw [depth_packet];omega
  have HL:=(IntegralMixedRoadmapCheckedCriticalTail.latest_layout
    (initial:=IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) HC HP).2.2
  rw [capture_count hn ht ha hR0 old hv hd left right R side] at HL
  exact HL

theorem compiled_program_length :(compiledProgram hn ht ha hR0 old hv hd left right R side).length=
    finishBirth hn ht ha hR0 old hv hd left right R side:=by
  have HL:=congrArg List.length (local_prefix_commands hn ht ha hR0 old hv hd left right R side)
  rw [paddedPast_length] at HL
  exact HL.symm

noncomputable def fullBirth:=IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n r

theorem full_birth_length :((PLAN).rules r).length=fullBirth hn ht ha hR0 old hv hd left right R side:=
  IntegralMixedMarkedPrefixFieldReadback.rules_length hn ht ha hR0 r

theorem full_birth :fullBirth hn ht ha hR0 old hv hd left right R side=
    finishBirth hn ht ha hR0 old hv hd left right R side+
      seedTailCount hn ht ha hR0 old hv hd left right R side:=by
  have HL:=congrArg List.length (full_commands hn ht ha hR0 old hv hd left right R side)
  rw [List.length_append,List.length_replicate,
    compiled_program_length hn ht ha hR0 old hv hd left right R side,
    full_birth_length hn ht ha hR0 old hv hd left right R side] at HL
  omega

theorem native_full_prefix :
    IntegralMixedFramedHistoryFamilyBits.prefixLength
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).parameters
      ((IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false).key
        (IntegralMixedRoadmapAtomic.context q))=fullBirth hn ht ha hR0 old hv hd left right R side:=by
  have HC:=IntegralMixedRoadmapCheckedProperMetadata.full_prefix hn ht ha hR0 q
  rw [initial_packet] at HC
  have HN:=prepared_initial hn ht ha hR0 old R.leftSpec R.rightSpec side
  have HR :IntegralMixedCausalRecordPlanBits.records r=
      IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q):=by
    unfold preparedRoot
    exact IntegralMixedRoadmapCheckedProperMetadata.root_records q
  unfold fullBirth IntegralMixedAuxiliaryMarkedRecordPlan.fullCount IntegralMixedCausalRecordPlanBits.count
  rw [HN,HR]
  exact HC

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
