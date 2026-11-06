/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperNoCriticalSound
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixFields
/-! # The reserved critical parent retains the actual original prefix roots

The provider and total record count stay fixed. The old word supplies roots
of the identical earlier observation, at the target's actual horizon.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank

noncomputable def originalBirth (q : List Bool) := FormulaSignSlotRadialProviderAtomic.initial q+
  IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)-1
noncomputable def preparedStart (q : List Bool) :=
  IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)-1
noncomputable def originalNaturalValues (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (i : ℕ) := originalField q hv (originalBirth q-1-i)

theorem base_records (q : List Bool) :
    IntegralMixedCausalRecordPlanBits.records (FormulaSignSlotRadialProviderAtomic.root q)=
      IntegralMixedRoadmapBadProbePacket.raw (IntegralMixedRoadmapProper.badPacket q) :=by
  rw [FormulaSignSlotRadialProviderAtomic.root_records]
  simp only [IntegralMixedRoadmapBadProbePacket.raw,IntegralMixedRoadmapProper.badPacket,
    IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair]
  rfl

theorem base_count (q : List Bool) :
    IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root q)=
      IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q) :=by
  unfold IntegralMixedCausalRecordPlanBits.count IntegralMixedRoadmapBadProbePacket.count
  rw [base_records]

theorem prepared_provider (q : List Bool) :
    FormulaSignSlotRadialProviderRecordPlan.providerContext (root q)=
      FormulaSignSlotRadialProviderAtomic.provider q := query_provider q []

theorem prepared_count (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    IntegralMixedCausalRecordPlanBits.count (root q)=
      IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root q) :=by
  change IntegralMixedCausalRecordPlanBits.count
    (IntegralMixedPhysicalCriticalQuery.root (query (pair q [])))=_
  rw [query_count,base_count]
  have H:=count_positive q hv
  omega

theorem prepared_records (q : List Bool) : IntegralMixedCausalRecordPlanBits.records (root q)=
    WordList.encode (IntegralMixedRoadmapBadProbePacket.prefixCodes (IntegralMixedRoadmapProper.badPacket q)++
      [IntegralMixedPhysicalCriticalQuery.normalize (code q)]) :=by
  unfold root canonical query IntegralMixedPhysicalCriticalQuery.packet
  simp only [pairFst_pair,pairSnd_pair,IntegralMixedPhysicalCriticalQuery.root]
  rw [IntegralMixedPhysicalCriticalQuery.prepare_records]
  simp only [IntegralMixedCausalRecordPlanBits.records,IntegralMixedPhysicalCriticalQuery.withEndpoints,
    prefixRoot,pairFst_pair,pairSnd_pair,IntegralMixedRoadmapBadProbePacket.prefixWord,
    WordListRecords.decode_encode]

theorem prepared_code (q : List Bool) (i : ℕ) (hi : i<preparedStart q) :
    IntegralMixedCausalRecordPlanBits.code (root q) i=
      IntegralMixedCausalRecordPlanBits.code (FormulaSignSlotRadialProviderAtomic.root q) i :=by
  have HL : i<(IntegralMixedRoadmapBadProbePacket.prefixCodes (IntegralMixedRoadmapProper.badPacket q)).length:=by
    simpa only [IntegralMixedRoadmapBadProbePacket.prefixCodes,List.length_map,List.length_range,preparedStart] using hi
  have hi' : i<IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProper.badPacket q)-1:=hi
  unfold IntegralMixedCausalRecordPlanBits.code
  rw [prepared_records,base_records,WordList.get_encode,List.getElem?_append_left HL]
  simp only [IntegralMixedRoadmapBadProbePacket.prefixCodes,List.getElem?_map,
    List.getElem?_range hi',Option.map_some,Option.getD_some]

theorem start_fit (q : List Bool) : preparedStart q≤
    IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root q) :=by
  rw [base_count]
  exact Nat.sub_le _ _

theorem prepared_prefix_roots (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    (FormulaSignSlotRadialProviderRecordPrefix.observation (root q) (preparedStart q)
      ((start_fit q).trans_eq (prepared_count q hv).symm)).Roots
        (FormulaSignSlotRadialProviderRecordPrefix.natural (FormulaSignSlotRadialProviderAtomic.root q)
          (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv)) :=by
  exact FormulaSignSlotRadialProviderRecordPrefix.transfer_word_roots
    (FormulaSignSlotRadialProviderAtomic.root q) (root q) (FormulaSignSlotRadialProviderAtomic.word q)
    (FormulaSignSlotRadialProviderAtomic.full_valid q hv)
    ((FormulaSignSlotRadialProviderAtomic.root_provider q).trans (prepared_provider q).symm)
    (prepared_count q hv).symm (preparedStart q) (start_fit q)
    (fun i hi=>(prepared_code q i hi).symm)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
