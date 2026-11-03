/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeShape
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeTest
public import LeanCanny.Encoding.IntegralMixedMarkedReservedRawRuling
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixFieldReadback
/-! # Native hint bytes select the actual ordinary current-Q parent rule -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeProvenance
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedRoadmapBadProbePacket
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap
 IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerPlan.degree
 IntegralMixedAuxiliaryMarkedIntegerSource.source IntegralMixedFramedRawHeight.rootCeiling
 IntegralMixedFramedNormalizationBits.requiredModulus
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H
local notation "dim"=>IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0)
local notation "ini"=>IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0)
local notation "wid"=>IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0)
local notation "ctx"=>IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0)
variable (z w : List Bool)
 (hh : HintGood (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0) z) z)
 (hb : IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha (radius_binary hR0) false
   (pair (IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0) z) w))
local notation "old"=>IntegralMixedVirtualTaskBits.saved P (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha (radius_binary hR0) false (ctx z))

theorem context_root :pairFst (ctx z)=preparedRoot (dim z) z:=pairFst_pair _ _
theorem context_birth : (IntegralMixedPhysicalCutOpenInterval.birthWord (ctx z)).length=creating (ini z) (pairFst z):=by
 simp only [IntegralMixedRoadmapBadProbeTest.intervalContext,intervalContext,
   IntegralMixedPhysicalCutOpenInterval.birthWord,pairSnd_pair,pairFst_pair,List.length_replicate]

theorem saved_root :pairFst old=preparedRoot (dim z) z:=
 (IntegralMixedFullHistoryFamilyBits.saved_root P _).trans
   ((IntegralMixedPhysicalCutLocalInterpretation.parent_root hn ht ha (radius_binary hR0) false (ctx z)).trans
     (context_root hn ht ha hR0 z))

theorem dimension_saved : (P).ambient (pairFst old)=dim z:=by
 change number n (pairFst old)+3=number n (root (pairFst z))+3
 rw [saved_root hn ht ha hR0 z,IntegralMixedRoadmapBadProbeFields.prepared_number]

include hh in
theorem creating_saved :creating (ini z) (pairFst z)=number n (pairFst old)+8+(prefixCodes (pairFst z)).length:=by
 have HI :ini z=number n (root (pairFst z))+8:=
   IntegralMixedRoadmapBadProbeFields.initial_eq hn ht ha (radius_binary hR0) (pairFst z)
 have HN :number n (pairFst old)=number n (root (pairFst z)):=by
   rw [saved_root hn ht ha hR0 z,IntegralMixedRoadmapBadProbeFields.prepared_number]
 simp only [creating,HI,HN,prefixCodes,List.length_map,List.length_range]
 have HC:=hh.1
 omega

include hh hb in
theorem prefix_saved :prefixLength P old=number n (pairFst old)+8+(prefixCodes (pairFst z)).length:=
 (family_birth P D H old).symm.trans
   ((IntegralMixedPhysicalCutLocalInterpretation.parent_birth hn ht ha (radius_binary hR0) false (ctx z) w hb).trans
     ((context_birth hn ht ha hR0 z).trans (creating_saved hn ht ha hR0 z hh)))

theorem records_saved :IntegralMixedCausalRecordPlanBits.records (pairFst old)=
    WordList.encode (prefixCodes (pairFst z)++[probe ((P).ambient (pairFst old)) z]):=by
 rw [saved_root hn ht ha hR0 z]
 have HD :=dimension_saved hn ht ha hR0 z
 rw [saved_root hn ht ha hR0 z] at HD
 rw [HD]
 simp only [IntegralMixedCausalRecordPlanBits.records,preparedRoot,pairSnd_pair,pairFst_pair,preparedRaw]

include hh in
theorem good_saved :IntegralMixedChronologicalCutCode.Good ((P).ambient (pairFst old))
    (number n (pairFst old)+8+(prefixCodes (pairFst z)).length) (labels (pairFst z))
      (WordListRecords.count (labels (pairFst z))+1) (Nat.fromBitsLE (field 1 z)):=by
 rw [dimension_saved hn ht ha hR0 z,←creating_saved hn ht ha hR0 z hh]
 exact IntegralMixedRoadmapBadProbeShape.raw_good (dim z) (ini z) (wid z) z hh

include hh hb in
theorem ordinary :IntegralMixedSelectedBadMembership.Ordinary ((G).rule old) ((G).kind old):=by
 have HT:=records_saved hn ht ha hR0 z
 change IntegralMixedCausalRecordPlanBits.records (pairFst old)=WordList.encode
   (prefixCodes (pairFst z)++[IntegralMixedChronologicalCutCode.code ((P).ambient (pairFst old))
     (labels (pairFst z)) (WordListRecords.count (labels (pairFst z))+1)
     (Nat.fromBitsLE (field 1 z)) (Nat.fromBitsLE (field 0 z))
     (Nat.fromBitsLE (field 2 z)) (Nat.fromBitsLE (field 3 z))]) at HT
 exact IntegralMixedMarkedReservedRuling.ordinary_raw hn ht ha hR0 old (prefixCodes (pairFst z))
   (labels (pairFst z)) _ _ _ _ _ (good_saved hn ht ha hR0 z hh) HT
   (prefix_saved hn ht ha hR0 z w hh hb) (IntegralMixedRoadmapBadProbeShape.tag_le _ _ _ z hh)

include hh hb in
theorem rule_raw :
    ∃h : IntegralMixedChronologicalCutCode.Good ((P).ambient (pairFst old)) ((G).birth old)
      (labels (pairFst z)) (WordListRecords.count (labels (pairFst z))+1) (Nat.fromBitsLE (field 1 z)),
    (G).rule old=(IntegralMixedChronologicalCutCode.rawData ((P).ambient (pairFst old)) ((G).birth old)
      (labels (pairFst z)) (WordListRecords.count (labels (pairFst z))+1) (Nat.fromBitsLE (field 1 z)) h).rule
        (commonDenominator ((G).state old)) (commonDenominator_ne_zero ((G).state old)):=by
 have HT:=records_saved hn ht ha hR0 z
 exact IntegralMixedMarkedReservedRuling.rule_raw hn ht ha hR0 old (prefixCodes (pairFst z))
   (labels (pairFst z)) _ _ _ _ _ (good_saved hn ht ha hR0 z hh) HT
   (prefix_saved hn ht ha hR0 z w hh hb) (IntegralMixedRoadmapBadProbeShape.tag_le _ _ _ z hh)

include hh in
theorem last_birth : (IntegralMixedPhysicalCutOpenInterval.birthWord (ctx z)).length+1=
    IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst (ctx z)):=by
 rw [context_birth hn ht ha hR0 z,context_root hn ht ha hR0 z]
 unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
 rw [prepared_count _ z hh.1,IntegralMixedRoadmapBadProbeFields.prepared_number]
 have HI :ini z=number n (root (pairFst z))+8:=
   IntegralMixedRoadmapBadProbeFields.initial_eq hn ht ha (radius_binary hR0) (pairFst z)
 unfold creating
 rw [HI]
 have HC:=hh.1
 omega

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeProvenance
