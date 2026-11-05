/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperWordValue
public import LeanCanny.Encoding.IntegralMixedRoadmapProperProbeMetadata
/-! # Guard metadata follows from actual row syntax without Atomic validity -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProperGuardMetadata
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedRoadmapProperRow
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR) false
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "D" => IntegralFramedBankQuery.Bank.plan B
local notation "H" => IntegralFramedBankQuery.Bank.data B
local notation "G" => IntegralMixedFramedHistoryFamilyBits.family P D H
attribute [local irreducible] creating parent terminal

theorem terminal_count (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    count hn ht ha hR mean z = creating hn ht ha hR z + 1 := by
  unfold count terminal
  change (IntegralMixedFramedBankSnapshotBits.atKey
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR))
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR))
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha (radius_binary hR))
    (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (context hn ht ha hR mean z))).count = _
  rw [IntegralMixedAuxiliaryMarkedRecordPlan.bank_count, context, pairFst_pair,
    IntegralMixedAuxiliaryMarkedRecordPlan.fullCount, root_number hn ht ha hR,
    root_count hn ht ha hR mean z hc]
  unfold creating IntegralMixedRoadmapBadProbePacket.creating
  omega

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

private theorem core (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z) :
    IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P (parent hn ht ha hR mean) z := by
  have HR := (rank_row_good_iff hn ht ha hR z).mpr hg
  have HD := parent_coordinate hn ht ha hR mean z HR
  have HA : (P).ambient (RankedHistoryTask.root (parent hn ht ha hR mean z)) = dimension hn ht ha hR z := by
    rw [parent_root, root_dimension]
  have HV : birth P (parent hn ht ha hR mean z) < (P).cap (RankedHistoryTask.root (parent hn ht ha hR mean z)) := by
    rw [parent_birth hn ht ha hR mean z hc, parent_root]
    unfold IntegralMixedPhysicalMarkedPlan.bank
    change creating hn ht ha hR z < IntegralMixedAuxiliaryMarkedIntegerSource.number n (root hn ht ha hR mean z) + 8 +
      IntegralMixedCausalRecordPlanBits.count (root hn ht ha hR mean z) + 2
    rw [root_number hn ht ha hR, root_count hn ht ha hR mean z hc]
    unfold creating IntegralMixedRoadmapBadProbePacket.creating
    omega
  refine ⟨⟨HV, ?_⟩, ?_⟩
  · change 2 ≤ get P .slot15 (parent hn ht ha hR mean z) ∧ get P .slot15 (parent hn ht ha hR mean z) ≤ 4
    rw [parent_context]
    exact ⟨by omega, by omega⟩
  · rw [HD, HA]
    exact (Nat.sub_le _ _).trans (Nat.le_of_lt HR.1.2.2.2.2)

private theorem metadata_indices (mean : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z)
    (c s : List Bool → ℕ) (hci : c z < count hn ht ha hR mean z) (hsi : s z < count hn ht ha hR mean z) :
    IntegralFramedPhysicalNear.Metadata P D H (parent hn ht ha hR mean) (terminal hn ht ha hR mean) c s z := by
  have HB : (G).birth (parentKey hn ht ha hR mean z) = creating hn ht ha hR z :=
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D H _).trans (parentKey_prefix hn ht ha hR mean z hc)
  refine ⟨core hn ht ha hR mean z hc hg, ?_, ?_, hci, hsi⟩
  · change (G).birth (parentKey hn ht ha hR mean z) ≤ count hn ht ha hR mean z
    rw [HB, terminal_count hn ht ha hR mean z hc]
    omega
  · rw [terminal, Function.comp_apply, context]
    change pairFst ((B).key (pair (root hn ht ha hR mean z) [])) = pairFst (parentKey hn ht ha hR mean z)
    rw [IntegralMixedPhysicalMarkedPlan.key_root, parentKey_root]

/-- No target Atomic.Valid premise is needed for either installed guard's
metadata: its indices are literal saturated newest-index selectors. -/
theorem near_metadata (right : Bool) (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z) :
    IntegralFramedPhysicalNear.Metadata P D H (parent hn ht ha hR false) (terminal hn ht ha hR false)
      (centerIndex hn ht ha hR right) (pointIndex hn ht ha hR false false) z := by
  apply metadata_indices hn ht ha hR false z hc hg
  · unfold centerIndex
    have HT := terminal_count hn ht ha hR false z hc
    omega
  · unfold pointIndex
    have HT := terminal_count hn ht ha hR false z hc
    omega

theorem rank_metadata (z : List Bool)
    (hc : 0 < IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) (hg : rankRowSyntax n z) :
    IntegralFramedPhysicalNear.Metadata P D H (parent hn ht ha hR true) (terminal hn ht ha hR true)
      (pointIndex hn ht ha hR true true) (pointIndex hn ht ha hR true true) z := by
  apply metadata_indices hn ht ha hR true z hc hg <;>
    unfold pointIndex <;>
    have HT := terminal_count hn ht ha hR true z hc <;> omega

end LeanCanny.Encoding.CoefficientMarkedRecordProperGuardMetadata
