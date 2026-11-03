/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRankNative
public import LeanCanny.Encoding.IntegralFramedZeroTarskiRank
/-! # The native mean-zero guard identifies an actual distinct-root rank

The interpreting hom is constructed from this query's own full word.
Numerical comparison with another root's ordinary sweep is a later step.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "hf"=>IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha (radius_binary hR0) false
local notation "hd"=>IntegralMixedPhysicalTraceCutTest.fallback hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters B) (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  parent terminal pointIndex IntegralFramedZeroTarskiStatistic.value

private theorem rankPacket_at (z w code : List Bool) :rankPacket hn ht ha hR0 (pair (pair z w) code)=
    IntegralFramedZeroTarskiStatistic.rankPacket (IntegralFramedBankQuery.Bank.parameters B) (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
      (IntegralFramedBankQuery.Bank.nodes B) (IntegralFramedBankQuery.Bank.factor B) (IntegralFramedBankQuery.Bank.seed B) (IntegralFramedBankQuery.Bank.bounds B) (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true)
      (pointIndex hn ht ha hR0 true true) (positive hn ht ha hR0 true) hf hd z w code :=by
  simp only [rankPacket,zeroStatistic,IntegralFramedPhysicalNear.reset,pairFst_pair,pairSnd_pair,
    IntegralFramedZeroTarskiStatistic.rankPacket]

variable (z w code : List Bool)
local notation "oldKey"=>IntegralMixedVirtualTaskBits.saved (IntegralFramedBankQuery.Bank.parameters B) (parent hn ht ha hR0 true z)
local notation "x"=>IntegralMixedCutSource.Family.state G oldKey
local notation "r"=>IntegralMixedCutSource.Family.rule G oldKey
local notation "j"=>IntegralMixedCoordinateCoefficientSnapshot.coordinate G oldKey
  (get (IntegralFramedBankQuery.Bank.parameters B) Field.slot13 (parent hn ht ha hR0 true z))
local notation "S"=>IntegralFramedPhysicalSquare.input (IntegralFramedBankQuery.Bank.parameters B) (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
  (IntegralFramedBankQuery.Bank.nodes B) (IntegralFramedBankQuery.Bank.factor B) (IntegralFramedBankQuery.Bank.seed B) (IntegralFramedBankQuery.Bank.bounds B) (terminal hn ht ha hR0 true) (positive hn ht ha hR0 true)
local notation "HM"=>IntegralFramedPhysicalNear.Metadata (IntegralFramedBankQuery.Bank.parameters B) (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
  (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true) (pointIndex hn ht ha hR0 true true)
  (pointIndex hn ht ha hR0 true true) z

noncomputable def RankAt (hm : HM) (hv : SquareSampleCompleteVertices.Valid S z w) : Prop:=
  IntegralFramedZeroTarskiStatistic.RankAt (IntegralFramedBankQuery.Bank.parameters B)
    (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B) (IntegralFramedBankQuery.Bank.nodes B)
    (IntegralFramedBankQuery.Bank.factor B) (IntegralFramedBankQuery.Bank.seed B) (IntegralFramedBankQuery.Bank.bounds B)
    (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true) (pointIndex hn ht ha hR0 true true)
    (positive hn ht ha hR0 true) z w code hv hm.2.1 hm.2.2.2.2

attribute [local irreducible] IntegralFramedZeroTarskiStatistic.RankAt

theorem rankLanguage_iff :pair (pair z w) code∈rankLanguage hn ht ha hR0↔
    ∃hm : HM,∃hv : SquareSampleCompleteVertices.Valid S z w,RankAt hn ht ha hR0 z w code hm hv :=by
  constructor
  · intro H
    have H' : HM ∧SquareSampleCompleteVertices.Valid S z w ∧RankAccept hn ht ha hR0 (pair (pair z w) code):=by
      simpa only [rankLanguage,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] using H
    obtain ⟨hm,hv,HA⟩:=H'
    refine ⟨hm,hv,?_⟩
    apply (IntegralFramedZeroTarskiStatistic.rankPacket_rankAt_iff (IntegralFramedBankQuery.Bank.parameters B)
      (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B) (IntegralFramedBankQuery.Bank.nodes B)
      (IntegralFramedBankQuery.Bank.factor B) (IntegralFramedBankQuery.Bank.seed B) (IntegralFramedBankQuery.Bank.bounds B)
      (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true) (pointIndex hn ht ha hR0 true true)
      (positive hn ht ha hR0 true) hf hd z w code hv hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.2).mp
    rw [←rankPacket_at hn ht ha hR0]
    exact HA
  · rintro ⟨hm,hv,HK⟩
    suffices HA : RankAccept hn ht ha hR0 (pair (pair z w) code) by
      simpa only [rankLanguage,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] using
        (show HM ∧SquareSampleCompleteVertices.Valid S z w ∧RankAccept hn ht ha hR0 (pair (pair z w) code) from ⟨hm,hv,HA⟩)
    change OrderedWindowStatisticBits.Accept (rankPacket hn ht ha hR0 (pair (pair z w) code))
    rw [rankPacket_at hn ht ha hR0]
    exact (IntegralFramedZeroTarskiStatistic.rankPacket_rankAt_iff (IntegralFramedBankQuery.Bank.parameters B)
      (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B) (IntegralFramedBankQuery.Bank.nodes B)
      (IntegralFramedBankQuery.Bank.factor B) (IntegralFramedBankQuery.Bank.seed B) (IntegralFramedBankQuery.Bank.bounds B)
      (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true) (pointIndex hn ht ha hR0 true true)
      (positive hn ht ha hR0 true) hf hd z w code hv hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.2).mpr HK

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
