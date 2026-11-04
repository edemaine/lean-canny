/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPastCritical
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendEndpointWordCriticalGuard
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendCriticalSuffix
/-! # Every creating critical stage accepts the same constructed proper word -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedFramedPhysicalIndex (arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)

private theorem correlation_at_birth (ctx w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false) ctx w)
    (a b :ℕ) (hab :a=b)
    (ha0 :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false ctx a)
    (hb0 :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false ctx b)
    (H :IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false ctx w hw a ha0=
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false ctx w hw a
        ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false ctx a,
          IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false ctx a ha0⟩):
    IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false ctx w hw b hb0=
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false ctx w hw b
        ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false ctx b,
          IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false ctx b hb0⟩:=by
  subst b
  exact H

variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "q0"=>packet D old R.leftSpec R.rightSpec side []
local notation "CTX"=>pair r []
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "mid"=>IntegralMixedRoadmapProper.midBirth
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q0) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q0) q0

noncomputable local instance properAppendAllCriticalIndexFintype :Fintype (Index (Fin 0) oldCs):=
  indexFintype (Fin 0) oldCs
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedPhysicalPointCompanionScan.geometricPoint IntegralMixedPhysicalPointCompanionScan.retained
  preparedRoot parentCommands IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus

private theorem allCritical_context :IntegralMixedRoadmapAtomic.context q0=CTX:=by
  simp only [IntegralMixedRoadmapAtomic.context,preparedRoot,IntegralMixedRoadmapAtomic.root,
    candidate_packet,payload_packet]

/-- Historical columns, the guarded endpoint trace, and the MID/CHILD/padding
readback prove the entire native scan on W's own full word. -/
theorem WordReceipt.all_critical {u :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    {pMID pChild :Fin ((P).ambient c+1)→ℝ}
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (hOld :∀idx<arity (parentCommands hn ht ha hR0 old R.leftSpec R.rightSpec side),
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 r W.word W.valid idx=
        oldNatural hn ht ha hR0 old hv idx):
    pair r W.word∈IntegralMixedPhysicalGuardScan.language hn ht ha (radius_binary hR0) false:=by
  have NP:=N
  unfold PhysicalReadback NativePair.PhysicalReadback at NP
  obtain ⟨A,E,layout,hLayout,HN⟩:=NP
  have GG :EndpointGuarded hn ht ha hR0 old hv hd left right R:=HN.endpoint_trace
  have HV:=physical_bank_values hn ht ha hR0 old hv hd left right R side u pMID pChild N
  apply (IntegralMixedPhysicalPointCompanionScan.all_critical_packet_iff hn ht ha (radius_binary hR0) false
    r W.word).mpr
  refine ⟨W.valid,?_⟩
  intro b hb hActive
  change b<IntegralMixedFramedHistoryFamilyBits.prefixLength (BK).parameters ((BK).key CTX) at hb
  have HF:=native_full_prefix hn ht ha hR0 old hv hd left right R side
  rw [allCritical_context hn ht ha hR0 old hv hd left right R side] at HF
  rw [HF] at hb
  by_cases hPast :b<beginBirth hn ht ha hR0 old
  · exact past_critical hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side
      (endpoints_good hn ht ha hR0 old hv hd left right R) W.word W.valid hOld b hPast hActive
  by_cases hMid :b<mid
  · let idx:=mid-1-b
    have HM:=midpoint_birth hn ht ha hR0 old hv hd left right R side
    have HI :idx<R.result.commands.length:=by dsimp only [idx];omega
    have HB :endpointBirth hn ht ha hR0 old hv hd left right R idx=b:=by
      unfold endpointBirth
      dsimp only [idx]
      omega
    have HA :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false CTX
        (endpointBirth hn ht ha hR0 old hv hd left right R idx):=by rw [HB];exact hActive
    have H:=W.endpoint_native_critical_guard hn ht ha hR0 old hv hd left right R side
      layout hLayout HN.pair_raw pMID pChild HV GG idx HI HA
    exact correlation_at_birth hn ht ha hR0 CTX W.word W.valid _ b HB HA hActive H
  · exact suffix_critical hn ht ha hR0 old hv hd left right R side u pMID pChild p0 N W b (by omega) hb hActive

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
