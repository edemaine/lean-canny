/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowParent
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowWitness
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicVertex

/-! # Both reserved row programs select their literal current-Q sweep data

The state and its denominator come from the actual saved creating prefix.
The zero stored degree does not certify a selected factor; these are
coefficient and ordered-statistic probes at the reserved final record.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family prefixLength)
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "D"=>IntegralFramedBankQuery.Bank.plan BK
local notation "H"=>IntegralFramedBankQuery.Bank.data BK
local notation "G"=>family P D H
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  dimension initial creating parentKey

noncomputable def parentDimension (mean : Bool) (z : List Bool):=(P).ambient (pairFst (parentKey hn ht ha hR0 mean z))
noncomputable def parentBirth (mean : Bool) (z : List Bool):=number n (pairFst (parentKey hn ht ha hR0 mean z))+8+
  (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)).length

theorem parentDimension_eq (mean : Bool) (z : List Bool) :
    parentDimension hn ht ha hR0 mean z=dimension hn ht ha hR0 z :=by
  rw [parentDimension,parentKey_root,root_dimension]

theorem parentBirth_eq (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    parentBirth hn ht ha hR0 mean z=creating hn ht ha hR0 z :=by
  rw [parentBirth,parentKey_root,root_number]
  simp only [IntegralMixedRoadmapBadProbePacket.prefixCodes,List.length_map,List.length_range,
    creating,IntegralMixedRoadmapBadProbePacket.creating]
  omega

noncomputable def ParentGood (mean : Bool) (z : List Bool):=
  IntegralMixedChronologicalCutCode.Good (parentDimension hn ht ha hR0 mean z)
    (parentBirth hn ht ha hR0 mean z) (labels z) (offset z) (coordinate z) ∧
  IntegralMixedChronologicalMidpointCode.Good (parentDimension hn ht ha hR0 mean z)
    (parentBirth hn ht ha hR0 mean z) (labels z) (oldProducer false z) (oldProducer true z) (offset z) (coordinate z)

theorem parent_good (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    ParentGood hn ht ha hR0 mean z :=by
  simpa only [ParentGood,parentDimension_eq,parentBirth_eq hn ht ha hR0 mean z hc,
    IntegralMixedRoadmapProperRowWitness.RowGood] using hg

noncomputable def parentData (mean : Bool) (z : List Bool) (hg : ParentGood hn ht ha hR0 mean z) :
    IntegralMixedCutRecordConstructor.Data (parentDimension hn ht ha hR0 mean z) (parentBirth hn ht ha hR0 mean z):=
  if mean then IntegralMixedChronologicalMeanCutCode.rawData _ _ (labels z)
    (oldProducer false z) (oldProducer true z) (offset z) (coordinate z) hg.2
  else IntegralMixedChronologicalCutCode.rawData _ _ (labels z) (offset z) (coordinate z) hg.1

theorem parentData_code (mean : Bool) (z : List Bool) (hg : ParentGood hn ht ha hR0 mean z) :
    (parentData hn ht ha hR0 mean z hg).code (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0=
      code hn ht ha hR0 mean z :=by
  cases mean
  · simp only [parentData,Bool.false_eq_true,ite_false]
    rw [IntegralMixedChronologicalCutCode.rawData_code _ _ _ _ _ hg.1 0 0 0 (by decide)]
    rw [parentDimension_eq]
    rfl
  · simp only [parentData,ite_true]
    rw [IntegralMixedChronologicalMeanCutCode.rawData_code,
      IntegralMixedChronologicalCutCode.ordinaryTag_index 0 (by decide),parentDimension_eq]
    rfl

theorem parentData_current (mean : Bool) (z : List Bool) (hg : ParentGood hn ht ha hR0 mean z) :
    (parentData hn ht ha hR0 mean z hg).current=true :=by
  cases mean <;> rfl

theorem parentData_slope (mean : Bool) (z : List Bool) (hg : ParentGood hn ht ha hR0 mean z)
    (Q : ℤ) (hQ : Q≠0) : ((parentData hn ht ha hR0 mean z hg).rule Q hQ).slope=Q :=by
  change (if (parentData hn ht ha hR0 mean z hg).current then Q else 1)=Q
  rw [parentData_current]
  rfl

attribute [local irreducible] parentData

private def Ruling (K : IntegralFramedBankQuery.Bank) (key : List Bool) (codes : List (List Bool)) : Prop :=
  ∀d : IntegralMixedCutRecordConstructor.Data (K.parameters.ambient (pairFst key))
      (number n (pairFst key)+8+codes.length),
    IntegralMixedCausalRecordPlanBits.records (pairFst key)=WordList.encode
      (codes++[d.code (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0])→
    prefixLength K.parameters key=number n (pairFst key)+8+codes.length→
    (family K.parameters K.plan K.data).rule key=d.rule
      (IntegralMixedHistory.commonDenominator ((family K.parameters K.plan K.data).state key))
      (IntegralMixedHistory.commonDenominator_ne_zero ((family K.parameters K.plan K.data).state key))

private theorem ruling_bridge (key : List Bool) (codes : List (List Bool)) :
    Ruling (n:=n) BK key codes :=by
  have HB : BK=IntegralMixedMarkedReservedParent.bank hn ht ha hR0:=by
    unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
    rfl
  have HR : Ruling (n:=n) (IntegralMixedMarkedReservedParent.bank hn ht ha hR0) key codes:=by
    intro d hrecords hprefix
    exact IntegralMixedMarkedReservedRuling.rule_eq hn ht ha hR0 key codes d
      (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0 hrecords hprefix
  exact (congrArg (fun K=>Ruling (n:=n) K key codes) HB).mpr HR

theorem rule_at_parent (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    (G).rule (parentKey hn ht ha hR0 mean z)=
      (parentData hn ht ha hR0 mean z (parent_good hn ht ha hR0 mean z hc hg)).rule
        (IntegralMixedHistory.commonDenominator ((G).state (parentKey hn ht ha hR0 mean z)))
        (IntegralMixedHistory.commonDenominator_ne_zero ((G).state (parentKey hn ht ha hR0 mean z))) :=by
  have HT : IntegralMixedCausalRecordPlanBits.records (pairFst (parentKey hn ht ha hR0 mean z))=
      WordList.encode (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)++
        [(parentData hn ht ha hR0 mean z (parent_good hn ht ha hR0 mean z hc hg)).code
          (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0]):=by
    rw [parentData_code]
    exact parentKey_records hn ht ha hR0 mean z
  have HK : prefixLength P (parentKey hn ht ha hR0 mean z)=parentBirth hn ht ha hR0 mean z:=
    (parentKey_prefix hn ht ha hR0 mean z hc).trans (parentBirth_eq hn ht ha hR0 mean z hc).symm
  exact ruling_bridge hn ht ha hR0 (parentKey hn ht ha hR0 mean z)
    (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z))
    (parentData hn ht ha hR0 mean z (parent_good hn ht ha hR0 mean z hc hg)) HT HK

theorem rule_current (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    ((G).rule (parentKey hn ht ha hR0 mean z)).slope=
      IntegralMixedHistory.commonDenominator ((G).state (parentKey hn ht ha hR0 mean z)) :=by
  rw [rule_at_parent hn ht ha hR0 mean z hc hg]
  exact parentData_slope hn ht ha hR0 mean z _ _ _

theorem row_count_positive (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z)) :
    0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z) :=by
  have HE : IntegralMixedRoadmapBadProbePacket.count (oldPacket z)=
      WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload (atomic z))):=by
    simp only [oldPacket,IntegralMixedRoadmapProper.badPacket,IntegralMixedRoadmapBadProbePacket.count,
      IntegralMixedRoadmapBadProbePacket.raw,IntegralMixedRoadmapBadProbePacket.packet,pairSnd_pair,pairFst_pair]
  rw [HE,IntegralMixedRoadmapAtomic.raw_count hn ht ha hR0 (atomic z) hv,
    IntegralMixedRoadmapRecordChain.probedRecordBound]
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
