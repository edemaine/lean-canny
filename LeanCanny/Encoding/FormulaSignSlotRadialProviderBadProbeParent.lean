/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeFields
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixSemantics
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshotBad
/-! # Ordinary bad sets agree on actual independently sampled provider parents -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeParent
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralMixedRoadmapBadProbePacket (root preparedRoot count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
local notation "C" => IntegralMixedCausalRecordPlanBits.count
local notation "ctx" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "S" => FormulaSignSlotRadialProviderAtomic.input

noncomputable def snapshot (r : List Bool) :=
  FormulaSignSlotRadialProviderRecordPrefix.snapshot r (C r-1) (Nat.sub_le _ _)
noncomputable def values (r w : List Bool) (hw : SquareSampleCompleteVertices.Valid S (ctx r) w) :=
  (FormulaSignSlotRadialProviderRecordPrefix.observation r (C r-1) (Nat.sub_le _ _)).point
    (FormulaSignSlotRadialProviderRecordPrefix.natural r w hw)
noncomputable def bad (r w labels : List Bool) (hw : SquareSampleCompleteVertices.Valid S (ctx r) w) : Set ℝ :=
  (snapshot r).bad labels (values r w hw)

theorem birth (r : List Bool) : (snapshot r).birth=N r+(C r-1) :=
  FormulaSignSlotRadialProviderRecordPrefix.snapshot_birth r (C r-1) (Nat.sub_le _ _)

theorem canonical (r : List Bool) : Canonical (snapshot r).state :=
  FormulaSignSlotRadialProviderRecordPrefix.snapshot_canonical r (C r-1) (Nat.sub_le _ _)

theorem realizes (r w : List Bool) (hw : SquareSampleCompleteVertices.Valid S (ctx r) w) :
    (snapshot r).Realizes (values r w hw) :=
  FormulaSignSlotRadialProviderRecordPrefix.snapshot_word_realizes r w hw (C r-1) (Nat.sub_le _ _)

theorem value_field (r w : List Bool) (hw : SquareSampleCompleteVertices.Valid S (ctx r) w)
    (i : ℕ) (hi : i<(snapshot r).birth) :
    values r w hw i=FormulaSignSlotRadialProviderAtomic.bankField (ctx r) w hw (N r+(C r-1)-1-i) :=
  FormulaSignSlotRadialProviderRecordPrefix.word_value r w hw (C r-1) (Nat.sub_le _ _) i (hi.trans_eq (birth r))

theorem snapshot_prepared (d : ℕ) (z : List Bool) (hc : 0<count (pairFst z)) :
    snapshot (root (pairFst z))=snapshot (preparedRoot d z) := by
  have H := FormulaSignSlotRadialProviderBadProbePrefix.prefix_snapshot d z hc (count (pairFst z)-1) (Nat.le_refl _)
  unfold snapshot
  simpa only [FormulaSignSlotRadialProviderBadProbePrefix.root_count,
    IntegralMixedRoadmapBadProbePacket.prepared_count d z hc] using H.symm

attribute [local irreducible] snapshot values FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.bank

theorem bad_eq_of_fields (d : ℕ) (z w : List Bool) (hc : 0<count (pairFst z))
    (hL : SquareSampleCompleteVertices.Valid S (ctx (root (pairFst z))) (IntegralMixedRoadmapBadProbePacket.word (pairFst z)))
    (hR : SquareSampleCompleteVertices.Valid S (ctx (preparedRoot d z)) w)
    (hf : FormulaSignSlotRadialProviderBadProbeFields.packet d (N (root (pairFst z))) z w∈
      FormulaSignSlotRadialProviderFieldEqualityList.language) :
    bad (root (pairFst z)) (IntegralMixedRoadmapBadProbePacket.word (pairFst z))
      (IntegralMixedRoadmapBadProbePacket.labels (pairFst z)) hL=
    bad (preparedRoot d z) w (IntegralMixedRoadmapBadProbePacket.labels (pairFst z)) hR := by
  have HF := (FormulaSignSlotRadialProviderBadProbeFields.packet_iff d _ z w hc rfl hL hR).mp hf
  unfold bad
  apply IntegralMixedPrefixSnapshot.Data.bad_transport _ _ (snapshot_prepared d z hc)
  intro i hi
  have HRight : i<(snapshot (preparedRoot d z)).birth := hi.trans_eq
    (congrArg IntegralMixedPrefixSnapshot.Data.birth (snapshot_prepared d z hc))
  rw [value_field _ _ hL i hi,value_field _ _ hR i HRight,
    FormulaSignSlotRadialProviderBadProbePrefix.prepared_initial,
    IntegralMixedRoadmapBadProbePacket.prepared_count d z hc,
    FormulaSignSlotRadialProviderBadProbePrefix.root_count]
  exact HF _ (by
    rw [birth,FormulaSignSlotRadialProviderBadProbePrefix.root_count] at hi
    unfold IntegralMixedRoadmapBadProbePacket.creating
    omega)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeParent
