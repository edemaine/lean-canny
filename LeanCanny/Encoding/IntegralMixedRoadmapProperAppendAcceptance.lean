/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendRawRetention
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendBeforeProbe
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendAllCritical
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendCompanions
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendGrammar
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendMarked
/-! # The sampled general append satisfies all seven native vertex conjuncts -/
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

noncomputable local instance properAppendAcceptanceIndexFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs

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

private theorem acceptance_packet_context (w :List Bool):
    IntegralMixedRoadmapAtomic.context (packet D old R.leftSpec R.rightSpec side w)=CTX:=by
  simp only [IntegralMixedRoadmapAtomic.context,IntegralMixedRoadmapAtomic.root,
    candidate_packet,payload_packet,preparedRoot]

private theorem acceptance_full_query (w :List Bool):
    IntegralMixedRoadmapAtomic.fullQuery (packet D old R.leftSpec R.rightSpec side w)=pair r w:=by
  simp only [IntegralMixedRoadmapAtomic.fullQuery,IntegralMixedRoadmapAtomic.root,
    candidate_packet,payload_packet,word_packet,preparedRoot]

theorem WordReceipt.atomic_valid {u :ℕ→ℝ} {p0 :Fin (AAmb+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    {pMID pChild :Fin (CAmb+1)→ℝ}
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (hOld :∀idx,idx<arity oldCs→u idx=oldNatural hn ht ha hR0 old hv idx):
    IntegralMixedRoadmapAtomic.Valid hn ht ha hR0
      (packet D old R.leftSpec R.rightSpec side W.word):=by
  have HOld:=W.old_raw hn ht ha hR0 old hv hd left right R side hOld
  have HW :SquareSampleCompleteVertices.Valid SI
      (IntegralMixedRoadmapAtomic.context (packet D old R.leftSpec R.rightSpec side W.word)) W.word:=
    Eq.mpr (congrArg (fun ctx=>SquareSampleCompleteVertices.Valid SI ctx W.word)
      (acceptance_packet_context hn ht ha hR0 old hv hd left right R side W.word)) W.valid
  have HG:=grammar hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side good W.word HW
  have HC :IntegralMixedAuxiliaryCandidate.Valid hn ht ha
      (IntegralMixedRoadmapAtomic.candidate (packet D old R.leftSpec R.rightSpec side W.word)):=by
    rw [candidate_packet]
    exact hv.2.1
  have HB:=W.before_probe hn ht ha hR0 old hv hd left right R side pMID pChild N HOld
  have HA:=W.all_critical hn ht ha hR0 old hv hd left right R side N HOld
  have HP:=W.child_companion hn ht ha hR0 old hv hd left right R side N
  have HM:=marked_of_raw_retention hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side good
    W.word W.valid HOld
  have HQ:=acceptance_full_query hn ht ha hR0 old hv hd left right R side W.word
  unfold IntegralMixedRoadmapAtomic.Valid
  refine ⟨HG,HC,?_,?_,?_,HP,?_⟩
  · simpa only [word_packet] using HW
  · exact Eq.mpr (congrArg (fun query=>query∈IntegralMixedPhysicalTraceBeforeProbe.language
      hn ht ha (radius_binary hR0) false) HQ) HB
  · exact Eq.mpr (congrArg (fun query=>query∈IntegralMixedPhysicalGuardScan.language
      hn ht ha (radius_binary hR0) false) HQ) HA
  · exact Eq.mpr (congrArg (fun query=>query∈IntegralMixedPhysicalMarkedTest.language
      hn ht ha (radius_binary hR0) false) HQ) HM

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
