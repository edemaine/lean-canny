/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendNoCut
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPastCut
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendMarkedRetention
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendLatestCompanion
/-! # One retained append satisfies the complete native vertex predicate -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "PLAN"=>IntegralFramedBankQuery.Bank.plan B
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "CTX"=>context hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedRoadmapAtomic.Grammar IntegralMixedRoadmapAtomic.dimension
  preparedRoot fullBirth

private theorem begin_eq_parent (old : List Bool) : beginBirth hn ht ha hR0 old=
    number n (IntegralMixedRoadmapAtomic.root old)+8+start hn ht ha hR0 old :=by
  have HI : IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old=
      number n (IntegralMixedRoadmapAtomic.root old)+8 :=by
    rw [IntegralMixedRoadmapAtomic.initial_eq]
    simp only [IntegralMixedAuxiliaryMarkedIntegerSource.number,
      IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
      IntegralMixedRoadmapAtomic.root,IntegralMixedRoadmapAtomic.original,pairFst_pair]
  unfold beginBirth IntegralMixedRoadmapAtomic.endBirth start
  rw [HI]

private theorem full_query_packet (old : List Bool) (e : ℕ) (w : List Bool) :
    IntegralMixedRoadmapAtomic.fullQuery (packet (D old) old e w)=pair (preparedRoot hn ht ha hR0 old e) w :=by
  rw [IntegralMixedRoadmapAtomic.fullQuery,packet_root,word_packet]

theorem before_probe_of_raw_retention (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S (CTX old e) w)
    (hr : ∀r<IntegralMixedFramedPhysicalIndex.arity (parentCommands hn ht ha hR0 old hv hd e he),
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 (preparedRoot hn ht ha hR0 old e) w hw r=
        oldNatural hn ht ha hR0 old hv r) :
    pair (preparedRoot hn ht ha hR0 old e) w∈
      IntegralMixedPhysicalTraceBeforeProbe.language hn ht ha (radius_binary hR0) false :=by
  refine ⟨?_,?_⟩
  · simpa only [IntegralMixedPhysicalMarkedTest.sampleContext,context,pairFst_pair,pairSnd_pair] using hw
  intro b hb hCut
  by_cases hOld : b<beginBirth hn ht ha hR0 old
  · exact past_cut hn ht ha hR0 old hv hd e he w hw hr b
      (hOld.trans_eq (begin_eq_parent hn ht ha hR0 old)) hCut
  · have HL:=IntegralMixedPhysicalTraceCutScan.count_eq_length hn ht ha (radius_binary hR0) false
      (preparedRoot hn ht ha hR0 old e) w
    have HJ : b<IntegralFramedTraceCutMetadata.length P PLAN (preparedRoot hn ht ha hR0 old e)+1 :=by omega
    have HC:=(IntegralFramedTraceCutOrigin.stageCut_iff P PLAN (pair (preparedRoot hn ht ha hR0 old e) w) b
      (by simpa only [pairFst_pair] using HJ)).mp hCut
    rw [pairFst_pair] at HC
    have HBirth:=IntegralMixedPhysicalTraceCutValidity.birth_count hn ht ha (radius_binary hR0) false
      (preparedRoot hn ht ha hR0 old e) w
    have HCount : IntegralMixedPhysicalTraceCutScan.count hn ht ha (radius_binary hR0) false
        (pair (preparedRoot hn ht ha hR0 old e) w)=fullBirth hn ht ha hR0 old e :=
      HBirth.symm.trans ((IntegralMixedFramedHistoryFamilyBits.family_birth P PLAN
        (IntegralFramedBankQuery.Bank.data B) ((B).key (CTX old e))).trans (prefix_length hn ht ha hR0 old e))
    have HB : b<fullBirth hn ht ha hR0 old e :=by omega
    exact False.elim (no_cut_after_begin hn ht ha hR0 old hv hd e he b (by omega) HB HC)

/-- All native conjuncts follow from the new word's actual columns and the
retention of the entire old natural tuple. No native guard is assumed. -/
theorem valid_of_retained_readback (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S (CTX old e) w)
    (p p0 : Fin ((P).ambient (pairFst ((B).key (CTX old e)))+1)→ℝ)
    (hr : FreshReadback hn ht ha hR0 old e w hw p p0)
    (hOld : ∀r<IntegralMixedFramedPhysicalIndex.arity (parentCommands hn ht ha hR0 old hv hd e he),
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 (preparedRoot hn ht ha hR0 old e) w hw r=
        oldNatural hn ht ha hR0 old hv r) :
    IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (packet (D old) old e w) :=by
  have HW : SquareSampleCompleteVertices.Valid S
      (IntegralMixedRoadmapAtomic.context (packet (D old) old e w)) w :=
    Eq.mpr (congrArg (fun c=>SquareSampleCompleteVertices.Valid S c w)
      (packet_context hn ht ha hR0 old e w)) hw
  have HG:=grammar hn ht ha hR0 old hv hd e he w HW
  have HC : IntegralMixedAuxiliaryCandidate.Valid hn ht ha
      (IntegralMixedRoadmapAtomic.candidate (packet (D old) old e w)) :=by
    rw [candidate_packet]
    exact hv.2.1
  have HB:=before_probe_of_raw_retention hn ht ha hR0 old hv hd e he w hw hOld
  have HA:=all_critical_of_past_and_fresh hn ht ha hR0 old e w hw p p0 hr
    (fun b hb hActive=>past_critical hn ht ha hR0 old hv hd e he w hw hOld b
      (hb.trans_eq (begin_eq_parent hn ht ha hR0 old)) hActive)
  have HP:=latest_companion_of_fresh_readback hn ht ha hR0 old hv hd e he w hw p p0 hr
  have HM:=marked_of_raw_retention hn ht ha hR0 old hv hd e he w hw hOld
  unfold IntegralMixedRoadmapAtomic.Valid
  refine ⟨HG,HC,?_,?_,?_,HP,?_⟩
  · simpa only [word_packet] using HW
  · exact Eq.mpr (congrArg (fun q=>q∈IntegralMixedPhysicalTraceBeforeProbe.language hn ht ha (radius_binary hR0) false)
      (full_query_packet hn ht ha hR0 old e w)) HB
  · exact Eq.mpr (congrArg (fun q=>q∈IntegralMixedPhysicalGuardScan.language hn ht ha (radius_binary hR0) false)
      (full_query_packet hn ht ha hR0 old e w)) HA
  · exact Eq.mpr (congrArg (fun q=>q∈IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false)
      (full_query_packet hn ht ha hR0 old e w)) HM

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
