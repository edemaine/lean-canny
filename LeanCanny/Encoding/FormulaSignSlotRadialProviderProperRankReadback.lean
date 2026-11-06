/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperNearNative
public import LeanCanny.Encoding.IntegralFramedZeroTarskiRank
/-! # The native mean-zero guard identifies an actual distinct-root rank

The interpreting hom is constructed from this provider query's own full word.
Numerical comparison with another root's ordinary sweep is a later step.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "hf"=>FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive
local notation "hd"=>FormulaSignSlotRadialProviderAtomic.Cuts.fallback
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters B) (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  parent terminal pointIndex IntegralFramedZeroTarskiStatistic.value

private theorem rankPacket_at (z w code : List Bool) :rankPacket (pair (pair z w) code)=
    IntegralFramedZeroTarskiStatistic.rankPacket (IntegralFramedBankQuery.Bank.parameters B) (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
      (IntegralFramedBankQuery.Bank.nodes B) (IntegralFramedBankQuery.Bank.factor B) (IntegralFramedBankQuery.Bank.seed B) (IntegralFramedBankQuery.Bank.bounds B) (parent true) (terminal true)
      (pointIndex true true) (positive true) hf hd z w code :=by
  simp only [rankPacket,zeroStatistic,IntegralFramedPhysicalNear.reset,pairFst_pair,pairSnd_pair,
    IntegralFramedZeroTarskiStatistic.rankPacket]

variable (z w code : List Bool)
local notation "oldKey"=>IntegralMixedVirtualTaskBits.saved (IntegralFramedBankQuery.Bank.parameters B) (parent true z)
local notation "x"=>IntegralMixedCutSource.Family.state G oldKey
local notation "r"=>IntegralMixedCutSource.Family.rule G oldKey
local notation "j"=>IntegralMixedCoordinateCoefficientSnapshot.coordinate G oldKey
  (get (IntegralFramedBankQuery.Bank.parameters B) Field.slot13 (parent true z))
local notation "S"=>IntegralFramedPhysicalSquare.input (IntegralFramedBankQuery.Bank.parameters B) (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
  (IntegralFramedBankQuery.Bank.nodes B) (IntegralFramedBankQuery.Bank.factor B) (IntegralFramedBankQuery.Bank.seed B) (IntegralFramedBankQuery.Bank.bounds B) (terminal true) (positive true)
local notation "HM"=>IntegralFramedPhysicalNear.Metadata (IntegralFramedBankQuery.Bank.parameters B) (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
  (parent true) (terminal true) (pointIndex true true)
  (pointIndex true true) z

noncomputable def RankAt (hm : HM) (hv : SquareSampleCompleteVertices.Valid S z w) : Prop:=
  IntegralFramedZeroTarskiStatistic.RankAt (IntegralFramedBankQuery.Bank.parameters B)
    (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B) (IntegralFramedBankQuery.Bank.nodes B)
    (IntegralFramedBankQuery.Bank.factor B) (IntegralFramedBankQuery.Bank.seed B) (IntegralFramedBankQuery.Bank.bounds B)
    (parent true) (terminal true) (pointIndex true true)
    (positive true) z w code hv hm.2.1 hm.2.2.2.2

attribute [local irreducible] IntegralFramedZeroTarskiStatistic.RankAt

theorem rankLanguage_iff :pair (pair z w) code∈rankLanguage↔
    ∃hm : HM,∃hv : SquareSampleCompleteVertices.Valid S z w,RankAt z w code hm hv :=by
  constructor
  · intro H
    have H' : HM ∧SquareSampleCompleteVertices.Valid S z w ∧RankAccept (pair (pair z w) code):=by
      simpa only [rankLanguage,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] using H
    obtain ⟨hm,hv,HA⟩:=H'
    refine ⟨hm,hv,?_⟩
    apply (IntegralFramedZeroTarskiStatistic.rankPacket_rankAt_iff (IntegralFramedBankQuery.Bank.parameters B)
      (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B) (IntegralFramedBankQuery.Bank.nodes B)
      (IntegralFramedBankQuery.Bank.factor B) (IntegralFramedBankQuery.Bank.seed B) (IntegralFramedBankQuery.Bank.bounds B)
      (parent true) (terminal true) (pointIndex true true)
      (positive true) hf hd z w code hv hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.2).mp
    rw [←rankPacket_at]
    exact HA
  · rintro ⟨hm,hv,HK⟩
    suffices HA : RankAccept (pair (pair z w) code) by
      simpa only [rankLanguage,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] using
        (show HM ∧SquareSampleCompleteVertices.Valid S z w ∧RankAccept (pair (pair z w) code) from ⟨hm,hv,HA⟩)
    change OrderedWindowStatisticBits.Accept (rankPacket (pair (pair z w) code))
    rw [rankPacket_at]
    exact (IntegralFramedZeroTarskiStatistic.rankPacket_rankAt_iff (IntegralFramedBankQuery.Bank.parameters B)
      (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B) (IntegralFramedBankQuery.Bank.nodes B)
      (IntegralFramedBankQuery.Bank.factor B) (IntegralFramedBankQuery.Bank.seed B) (IntegralFramedBankQuery.Bank.bounds B)
      (parent true) (terminal true) (pointIndex true true)
      (positive true) hf hd z w code hv hm.1 hm.2.1 hm.2.2.1 hm.2.2.2.2).mpr HK

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
