/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPhysical
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPastCut
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendEndpointWordCutGuard
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedCriticalTail
/-! # Actual before-probe guards follow from old raw retention and one proper-level witness -/
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

noncomputable local instance properAppendBeforeProbeIndexFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  preparedRoot parentCommands parentState IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth

local notation "q"=>packet D old R.leftSpec R.rightSpec side []
local notation "K"=>List.length (R.orderedFree hk)

local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "SI"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX"=>pair r []
local notation "CAmb"=>IntegralCriticalHistoryTask.Parameters.ambient P c
local notation "AAmb"=>IntegralCriticalHistoryTask.Parameters.ambient P r
local notation "S0"=>IntegralCriticalHistoryTask.Parameters.cap P c+1
local notation "BW0"=>IntegralCriticalHistoryTask.Parameters.width P c
local notation "hQ0"=>IntegralMixedStaticRecordPrefix.cap (Q c) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c)
local notation "L0"=>IntegralMixedFramedPhysicalIndex.arity
  (List.append (α:=Instruction CAmb BW0)
    (R.result.commands.map (IntegralMixedFramedFixedContinuation.wrap (Q c) hQ0)) oldCs)
local notation "mid0"=>List.length oldCs+R.result.commands.length
local notation "mid"=>IntegralMixedRoadmapProper.midBirth
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
  (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q
local notation "key"=>IntegralFramedBankQuery.Bank.key BK CTX
open IntegralMixedFramedPhysicalIndex (arity prefixArity enumerate)

local notation "PP"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "PD"=>IntegralFramedBankQuery.Bank.plan BK
attribute [local irreducible] PhysicalReadback NativePair.PhysicalReadback
  EndpointGuarded IntegralMixedPhysicalFieldEquality.point

/-- The same natural readback already contains the genuinely guarded endpoint
program; no endpoint native guard is supplied to this theorem. -/
theorem physical_endpoint_guarded (u :ℕ→ℝ) (pMID pChild :Fin (CAmb+1)→ℝ)
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild):
    EndpointGuarded hn ht ha hR0 old hv hd left right R:=by
  unfold PhysicalReadback NativePair.PhysicalReadback at N
  obtain ⟨A,E,ordinal,hen,HN⟩:=N
  unfold EndpointGuarded
  exact HN.endpoint_trace

private theorem actual_trace_length (root :List Bool):
    IntegralFramedTraceCutMetadata.length PP PD root=IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
  unfold IntegralFramedTraceCutMetadata.length IntegralMixedPhysicalMarkedPlan.bank
    IntegralMixedAuxiliaryMarkedRecordPlan.bank
  exact IntegralMixedMarkedPrefixFieldReadback.rules_length hn ht ha hR0 root

private theorem certified_cut_iff (root :List Bool) (b :ℕ):
    IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt PP PD root b).command↔
      IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt P PLAN root b).command:=by
  unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank
  rfl

private theorem no_cut_suffix (b :ℕ) (hb0 :mid≤b)
    (hb1 :b<fullBirth hn ht ha hR0 old hv hd left right R side):
    ¬IntegralFramedCreatingCut.IsCut (IntegralMixedFramedRootPullback.instructionAt PP PD r b).command:=by
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
  have H:=IntegralMixedRoadmapCheckedCriticalTail.no_cut_after_mid hn ht ha hR0 q HC HP HD b hb0
    (by rw [native_full_prefix hn ht ha hR0 old hv hd left right R side];exact hb1)
  have HR :IntegralMixedRoadmapAtomic.root q=r:=by unfold preparedRoot;rfl
  rw [HR] at H
  exact fun h=>H ((certified_cut_iff hn ht ha hR0 r b).mp h)

/-- Every actual cut before the reserved probe is checked on W's own root and
word. Only literal old natural-column retention is needed beyond W and N. -/
theorem WordReceipt.before_probe {u :ℕ→ℝ} {p0 :Fin (AAmb+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (pMID pChild :Fin (CAmb+1)→ℝ)
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (hOld :∀idx<arity (parentCommands hn ht ha hR0 old R.leftSpec R.rightSpec side),
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 r W.word W.valid idx=
        oldNatural hn ht ha hR0 old hv idx):
    pair r W.word∈IntegralMixedPhysicalTraceBeforeProbe.language hn ht ha (radius_binary hR0) false:=by
  have GG:=physical_endpoint_guarded hn ht ha hR0 old hv hd left right R side u pMID pChild N
  have hValues :∀idx :Fin ((oldCs).length+R.result.commands.length+1+K+1+K),
      (canonicalObservation hn ht ha hR0 old hv hd left right R side).point u idx.val=
        IntegralMixedChronologicalLevelScalarValues.levelValues pMID pChild R.result.nextValues g (R.orderedFree hk) idx:=by
    intro idx
    exact physical_bank_values hn ht ha hR0 old hv hd left right R side u pMID pChild N idx
  refine ⟨?_,?_⟩
  · simpa only [IntegralMixedPhysicalMarkedTest.sampleContext,pairFst_pair,pairSnd_pair] using W.valid
  intro b hb hCut
  have HL:=IntegralMixedPhysicalTraceCutScan.count_eq_length hn ht ha (radius_binary hR0) false r W.word
  have HJ :b<IntegralFramedTraceCutMetadata.length PP PD r+1:=by omega
  have HCount :IntegralMixedPhysicalTraceCutScan.count hn ht ha (radius_binary hR0) false (pair r W.word)=
      fullBirth hn ht ha hR0 old hv hd left right R side:=
    HL.trans (actual_trace_length hn ht ha hR0 r)
  have HFull :b<fullBirth hn ht ha hR0 old hv hd left right R side:=by omega
  by_cases hPast :b<beginBirth hn ht ha hR0 old
  · exact past_cut hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side good W.word W.valid hOld b hPast hCut
  by_cases hMid :b<mid
  · let idx:=mid-1-b
    have HM:=midpoint_birth hn ht ha hR0 old hv hd left right R side
    have HI :idx<R.result.commands.length:=by dsimp only [idx];omega
    have HB :endpointBirth hn ht ha hR0 old hv hd left right R idx=b:=by
      unfold endpointBirth
      dsimp only [idx]
      omega
    have HC :IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha (radius_binary hR0) false
        (IntegralFramedTraceCutScan.stagePacket (pair r W.word)
          (endpointBirth hn ht ha hR0 old hv hd left right R idx)):=by rw [HB];exact hCut
    have H:=W.endpoint_native_cut_guard hn ht ha hR0 old hv hd left right R side pMID pChild hValues GG idx HI HC
    rw [HB] at H
    exact H
  · have HC:=(IntegralFramedTraceCutOrigin.stageCut_iff PP PD (pair r W.word) b
      (by simpa only [pairFst_pair] using HJ)).mp hCut
    rw [pairFst_pair] at HC
    exact False.elim (no_cut_suffix hn ht ha hR0 old hv hd left right R side b (by omega) HFull HC)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
