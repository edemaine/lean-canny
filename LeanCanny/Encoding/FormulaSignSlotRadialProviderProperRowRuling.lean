/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowParent
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowWitness
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicPoint
public import LeanCanny.Encoding.IntegralMixedReservedCutModuloInstruction
public import LeanCanny.Encoding.IntegralMixedChronologicalMeanCutRaw

/-! # Both reserved row programs select their literal current-Q sweep data

The state and its denominator come from the actual saved creating prefix.
The zero stored degree does not certify a selected factor; these are
coefficient and ordered-statistic probes at the reserved final record.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family prefixLength)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "BK"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "D"=>IntegralFramedBankQuery.Bank.plan BK
local notation "H"=>IntegralFramedBankQuery.Bank.data BK
local notation "G"=>family P D H
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  dimension initial creating parentKey

noncomputable def parentDimension (mean : Bool) (z : List Bool):=(P).ambient (pairFst (parentKey mean z))
noncomputable def parentBirth (mean : Bool) (z : List Bool):=FormulaSignSlotRadialProviderRecordPlan.count (pairFst (parentKey mean z))+
  (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)).length

theorem parentDimension_eq (mean : Bool) (z : List Bool) :
    parentDimension mean z=dimension z :=by
  rw [parentDimension,parentKey_root,root_dimension]

theorem parentBirth_eq (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    parentBirth mean z=creating z :=by
  rw [parentBirth,parentKey_root,root_initial]
  simp only [IntegralMixedRoadmapBadProbePacket.prefixCodes,List.length_map,List.length_range,
    creating,IntegralMixedRoadmapBadProbePacket.creating]
  omega

noncomputable def ParentGood (mean : Bool) (z : List Bool):=
  IntegralMixedChronologicalCutCode.Good (parentDimension mean z)
    (parentBirth mean z) (labels z) (offset z) (coordinate z) ∧
  IntegralMixedChronologicalMidpointCode.Good (parentDimension mean z)
    (parentBirth mean z) (labels z) (oldProducer false z) (oldProducer true z) (offset z) (coordinate z)

theorem parent_good (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    ParentGood mean z :=by
  simpa only [ParentGood,parentDimension_eq,parentBirth_eq mean z hc,
    FormulaSignSlotRadialProviderProperRowWitness.RowGood] using hg

noncomputable def parentData (mean : Bool) (z : List Bool) (hg : ParentGood mean z) :
    IntegralMixedCutRecordConstructor.Data (parentDimension mean z) (parentBirth mean z):=
  if mean then IntegralMixedChronologicalMeanCutCode.rawData _ _ (labels z)
    (oldProducer false z) (oldProducer true z) (offset z) (coordinate z) hg.2
  else IntegralMixedChronologicalCutCode.rawData _ _ (labels z) (offset z) (coordinate z) hg.1

theorem parentData_code (mean : Bool) (z : List Bool) (hg : ParentGood mean z) :
    (parentData mean z hg).code (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0=
      code mean z :=by
  cases mean
  · simp only [parentData,Bool.false_eq_true,ite_false]
    rw [IntegralMixedChronologicalCutCode.rawData_code _ _ _ _ _ hg.1 0 0 0 (by decide)]
    rw [parentDimension_eq]
    rfl
  · simp only [parentData,ite_true]
    rw [IntegralMixedChronologicalMeanCutCode.rawData_code,
      IntegralMixedChronologicalCutCode.ordinaryTag_index 0 (by decide),parentDimension_eq]
    rfl

theorem parentData_current (mean : Bool) (z : List Bool) (hg : ParentGood mean z) :
    (parentData mean z hg).current=true :=by
  cases mean <;> rfl

theorem parentData_slope (mean : Bool) (z : List Bool) (hg : ParentGood mean z)
    (Q : ℤ) (hQ : Q≠0) : ((parentData mean z hg).rule Q hQ).slope=Q :=by
  change (if (parentData mean z hg).current then Q else 1)=Q
  rw [parentData_current]
  rfl

attribute [local irreducible] parentData

private theorem rule_view (Q : Parameters) (E : IntegralMixedFramedHistoryFamilyBits.Plan Q)
    (J : IntegralMixedFramedHistoryFamilyBits.Data Q E) (key : List Bool) (m : ℕ)
    (d : IntegralMixedCutRecordConstructor.Data (Q.ambient (pairFst key)) m) :
    d.rule (IntegralMixedHistory.commonDenominator (IntegralMixedFramedFamilyRunView.stateView Q E J key))
      (IntegralMixedHistory.commonDenominator_ne_zero _)=
    d.rule (IntegralMixedHistory.commonDenominator ((family Q E J).state key))
      (IntegralMixedHistory.commonDenominator_ne_zero _) :=rfl

private def Ruling (K : IntegralFramedBankQuery.Bank) (key : List Bool) (codes : List (List Bool)) : Prop :=
  ∀d : IntegralMixedCutRecordConstructor.Data (K.parameters.ambient (pairFst key))
      (FormulaSignSlotRadialProviderRecordPlan.count (pairFst key)+codes.length),
    IntegralMixedCausalRecordPlanBits.records (pairFst key)=WordList.encode
      (codes++[d.code (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0])→
    prefixLength K.parameters key=FormulaSignSlotRadialProviderRecordPlan.count (pairFst key)+codes.length→
    (family K.parameters K.plan K.data).rule key=d.rule
      (IntegralMixedHistory.commonDenominator (IntegralMixedFramedFamilyRunView.stateView K.parameters K.plan K.data key))
      (IntegralMixedHistory.commonDenominator_ne_zero (IntegralMixedFramedFamilyRunView.stateView K.parameters K.plan K.data key))

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPlan.factor FormulaSignSlotRadialProviderRecordPlan.seed
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
attribute [local semireducible] FormulaSignSlotRadialProviderRecordPlan.bank in
private theorem ruling_bridge (key : List Bool) (codes : List (List Bool)) :
    Ruling BK key codes :=by
  intro d hrecords hprefix
  exact IntegralMixedReservedCutModuloInstruction.rule_at_parent P
    (fun root _=>FormulaSignSlotRadialProviderRecordPlan.spatial root)
    FormulaSignSlotRadialProviderRecordPlan.positive
    (fun root _=>FormulaSignSlotRadialProviderRecordPlan.spatial_degree root)
    FormulaSignSlotRadialProviderRecordPlan.spatial_cap FormulaSignSlotRadialProviderRecordPlan.count
    FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.source_nonzero
    FormulaSignSlotRadialProviderRecordPlan.source_degree_cap FormulaSignSlotRadialProviderRecordPlan.room
    H key codes d (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0 hrecords hprefix

theorem rule_at_parent (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    (G).rule (parentKey mean z)=
      (parentData mean z (parent_good mean z hc hg)).rule
        (IntegralMixedHistory.commonDenominator ((G).state (parentKey mean z)))
        (IntegralMixedHistory.commonDenominator_ne_zero ((G).state (parentKey mean z))) :=by
  have HT : IntegralMixedCausalRecordPlanBits.records (pairFst (parentKey mean z))=
      WordList.encode (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)++
        [(parentData mean z (parent_good mean z hc hg)).code
          (IntegralMixedChronologicalCutCode.ordinaryTag 0) 0 0]):=by
    rw [parentData_code]
    exact parentKey_records mean z
  have HK : prefixLength P (parentKey mean z)=parentBirth mean z:=
    (parentKey_prefix mean z hc).trans (parentBirth_eq mean z hc).symm
  have HR:=ruling_bridge (parentKey mean z)
    (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z))
    (parentData mean z (parent_good mean z hc hg)) HT HK
  exact HR.trans (rule_view P D H (parentKey mean z) _ _)

theorem rule_current (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z))
    (hg : FormulaSignSlotRadialProviderProperRowWitness.RowGood z) :
    ((G).rule (parentKey mean z)).slope=
      IntegralMixedHistory.commonDenominator ((G).state (parentKey mean z)) :=by
  rw [rule_at_parent mean z hc hg]
  exact parentData_slope mean z _ _ _

theorem row_count_positive (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) :
    0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z) :=by
  have HE : IntegralMixedRoadmapBadProbePacket.count (oldPacket z)=
      WordListRecords.count (IntegralMixedRoadmapChain.raw (FormulaSignSlotRadialProviderAtomic.payload (atomic z))):=by
    simp only [oldPacket,IntegralMixedRoadmapProper.badPacket,IntegralMixedRoadmapBadProbePacket.count,
      IntegralMixedRoadmapBadProbePacket.raw,IntegralMixedRoadmapBadProbePacket.packet,pairSnd_pair,pairFst_pair,
      FormulaSignSlotRadialProviderAtomic.payload,IntegralMixedRoadmapAtomic.payload]
  rw [HE,FormulaSignSlotRadialProviderAtomic.raw_count (atomic z) hv.1,
    IntegralMixedRoadmapRecordChain.probedRecordBound]
  omega

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
