/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixMetadata
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeSearch
/-! # Reserved bad probes preserve the actual provider parent prefix -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbePrefix
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedRoadmapBadProbePacket (root preparedRoot count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "provider" => FormulaSignSlotRadialProviderRecordPlan.providerContext
local notation "C" => IntegralMixedCausalRecordPlanBits.count

theorem root_count (base : List Bool) : C (root base)=count base := by
  simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
    root,count,pairSnd_pair,pairFst_pair]

theorem prepared_provider (n : ℕ) (z : List Bool) :
    provider (preparedRoot n z)=provider (root (pairFst z)) := by
  simp only [FormulaSignSlotRadialProviderRecordPlan.providerContext,preparedRoot,root,pairFst_pair]

theorem prepared_count (n : ℕ) (z : List Bool) (hc : 0<count (pairFst z)) :
    C (preparedRoot n z)=C (root (pairFst z)) :=
  (IntegralMixedRoadmapBadProbePacket.prepared_count n z hc).trans (root_count (pairFst z)).symm

theorem prepared_record (n : ℕ) (z : List Bool) (i : ℕ) (hi : i<count (pairFst z)-1) :
    IntegralMixedCausalRecordPlanBits.code (preparedRoot n z) i=
      IntegralMixedCausalRecordPlanBits.code (root (pairFst z)) i := by
  unfold IntegralMixedCausalRecordPlanBits.code IntegralMixedCausalRecordPlanBits.records
  simp only [preparedRoot,root,pairSnd_pair,pairFst_pair]
  exact IntegralMixedRoadmapBadProbePacket.prepared_lookup n z i hi

theorem prepared_initial (n : ℕ) (z : List Bool) :
    FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot n z)=
      FormulaSignSlotRadialProviderRecordPlan.count (root (pairFst z)) :=
  FormulaSignSlotRadialProviderRecordPrefix.count_eq _ _ (prepared_provider n z)

theorem prepared_cap (n : ℕ) (z : List Bool) (hc : 0<count (pairFst z)) :
    FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.cap (preparedRoot n z)=
      FormulaSignSlotRadialProviderRecordPlan.certifiedParameters.cap (root (pairFst z)) :=
  FormulaSignSlotRadialProviderRecordPrefix.cap _ _ (prepared_provider n z) (prepared_count n z hc)

theorem prefix_fit (n : ℕ) (z : List Bool) (hc : 0<count (pairFst z))
    (j : ℕ) (hj : j≤count (pairFst z)-1) : j≤C (preparedRoot n z) := by
  rw [prepared_count n z hc,root_count]
  omega

theorem prefix_snapshot (n : ℕ) (z : List Bool) (hc : 0<count (pairFst z))
    (j : ℕ) (hj : j≤count (pairFst z)-1) :
    FormulaSignSlotRadialProviderRecordPrefix.snapshot (preparedRoot n z) j (prefix_fit n z hc j hj)=
      FormulaSignSlotRadialProviderRecordPrefix.snapshot (root (pairFst z)) j
        ((prefix_fit n z hc j hj).trans_eq (prepared_count n z hc)) :=
  FormulaSignSlotRadialProviderRecordPrefix.snapshot_eq _ _ (prepared_provider n z)
    (prepared_count n z hc) j (prefix_fit n z hc j hj)
    (fun i hi=>prepared_record n z i (hi.trans_le hj))

theorem prefix_observation (n : ℕ) (z : List Bool) (hc : 0<count (pairFst z))
    (j : ℕ) (hj : j≤count (pairFst z)-1) :
    FormulaSignSlotRadialProviderRecordPrefix.observation (preparedRoot n z) j (prefix_fit n z hc j hj)=
      FormulaSignSlotRadialProviderRecordPrefix.observation (root (pairFst z)) j
        ((prefix_fit n z hc j hj).trans_eq (prepared_count n z hc)) :=
  FormulaSignSlotRadialProviderRecordPrefix.observation_eq _ _ (prepared_provider n z)
    (prepared_count n z hc) j (prefix_fit n z hc j hj)
    (fun i hi=>prepared_record n z i (hi.trans_le hj))

end LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbePrefix
