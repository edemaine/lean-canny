/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendWindows
public import LeanCanny.Algebra.IntegralMixedFramedCriticalPrefixArity
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedCriticalTail
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendParentColumns
public import LeanCanny.Algebra.IntegralMixedPrefixProgramTransport
public import LeanCanny.Encoding.IntegralMixedMarkedConstructedPrefix
public import LeanCanny.Encoding.IntegralMixedMarkedSeedTailVertex
/-! # Exact native physical arity throughout a proper append critical suffix -/
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

noncomputable local instance properAppendPhysicalArityIndexFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  preparedRoot parentCommands parentState IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth

local notation "q"=>packet D old R.leftSpec R.rightSpec side []
local notation "K"=>List.length (R.orderedFree hk)

local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "PP"=>IntegralFramedBankQuery.Bank.parameters B
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "key"=>IntegralFramedBankQuery.Bank.key B (IntegralMixedRoadmapAtomic.context q)
local notation "mid"=>IntegralMixedRoadmapProper.midBirth
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
  (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q
open IntegralMixedFramedPhysicalIndex

private theorem actual_rules_length (root :List Bool) :((B).plan.rules root).length=((PLAN).rules root).length:=by
  unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank
  rfl

private theorem actual_rules_arity (root :List Bool) :arity ((B).plan.rules root)=arity ((PLAN).rules root):=by
  unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank
  rfl

theorem native_root :pairFst key=r:=by
  rw [IntegralMixedPhysicalFieldEquality.key_root hn ht ha (radius_binary hR0),
    IntegralMixedRoadmapAtomic.context,pairFst_pair]
  unfold preparedRoot
  rfl

theorem native_dimension :(PP).ambient (pairFst key)=D:=by
  rw [native_root hn ht ha hR0 old hv hd left right R side]
  have H:=prepared_dimension hn ht ha hR0 old R.leftSpec R.rightSpec side
  unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank
  exact H

theorem new_header_context (b :ℕ) (hb0 :mid≤b)
    (hb1 :b<fullBirth hn ht ha hR0 old hv hd left right R side):
    (IntegralMixedCommandHeaderBits.lookup ((T).commands (pairFst key)) b).context=1:=by
  have HC0:=pair_checked hn ht ha hR0 old hv hd left right R side []
  have HC :IntegralMixedRoadmapChain.Checked
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha q) (IntegralMixedRoadmapAtomic.payload q):=by
    rw [dimension_packet,initial_packet,payload_packet]
    simpa only [IntegralMixedRoadmapAtomic.scalarBudget,original_packet] using HC0
  have HP :IntegralMixedRoadmapChain.probe (IntegralMixedRoadmapAtomic.payload q)=
      IntegralMixedRoadmapChain.seedCode (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q):=by
    rw [payload_packet,dimension_packet]
    unfold payload
    exact IntegralMixedRoadmapChain.append_seed_probe _ _ _ _ _
  have HD :0<IntegralMixedRoadmapAtomic.depth q:=by rw [depth_packet];omega
  have HB :b<IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters key:=by
    rw [native_full_prefix hn ht ha hR0 old hv hd left right R side]
    exact hb1
  have H:=(IntegralMixedRoadmapCheckedCriticalTail.active_after_mid hn ht ha hR0 q HC HP HD b hb0 HB).2
  change (IntegralMixedFramedCriticalGuardBits.header T
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) IntegralFramedPhysicalCriticalGuardScan.stage
    (pair (IntegralMixedRoadmapAtomic.context q) (List.replicate b true))).context=1 at H
  simpa only [IntegralMixedFramedCriticalGuardBits.header,IntegralFramedPhysicalCriticalGuardTest.keyDatum,
    IntegralFramedPhysicalCriticalGuardScan.stage,pairFst_pair,pairSnd_pair,List.length_replicate] using H

theorem prefix_arity_after_mid (b :ℕ) (hb0 :mid≤b)
    (hb1 :b≤fullBirth hn ht ha hR0 old hv hd left right R side):
    prefixArity PP T (pair key (List.replicate b true))=
      prefixArity PP T (pair key (List.replicate mid true))+(2*D+4)*(b-mid):=by
  rw [prefixArity_critical_interval PP T key mid b hb0
    (fun z hz0 hz1=>new_header_context hn ht ha hR0 old hv hd left right R side z hz0 (hz1.trans_le hb1)),
    native_dimension hn ht ha hR0 old hv hd left right R side]

theorem prefix_arity_finish :
    prefixArity PP T (pair key (List.replicate (finishBirth hn ht ha hR0 old hv hd left right R side) true))=
      arity (compiledProgram hn ht ha hR0 old hv hd left right R side):=by
  rw [prefixArity_packet PP (B).plan (B).data T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false),
    native_root hn ht ha hR0 old hv hd left right R side]
  unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank
  exact congrArg arity (local_prefix_commands hn ht ha hR0 old hv hd left right R side)

theorem prefix_arity_full :
    prefixArity PP T (pair key (List.replicate (fullBirth hn ht ha hR0 old hv hd left right R side) true))=
      arity ((PLAN).rules r):=by
  rw [prefixArity_packet PP (B).plan (B).data T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false),
    native_root hn ht ha hR0 old hv hd left right R side]
  have HL :((B).plan.rules r).length=fullBirth hn ht ha hR0 old hv hd left right R side:=
    (actual_rules_length hn ht ha hR0 r).trans (full_birth_length hn ht ha hR0 old hv hd left right R side)
  rw [←HL,paddedPast_full]
  exact actual_rules_arity hn ht ha hR0 r

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
