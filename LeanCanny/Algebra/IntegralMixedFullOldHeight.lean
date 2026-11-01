/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNativeOldHeight
/-! # Actual creating tags and coordinates of every mixed old-height child -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFullHistoryScript IntegralMixedOldHeightBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def commandContext (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (root : List Bool) (b : ℕ) :=
  ((chronological (D.rules root) b).getD defaultCommand).context
noncomputable def commandCoordinate (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (root : List Bool) (b : ℕ) :=
  ((chronological (D.rules root) b).getD defaultCommand).coordinate

theorem creating_context_snapshot (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) :
    (IntegralMixedFullHistoryFamilyBits.creatingCommand P D key).context =
      commandContext P D (pairFst key) (IntegralMixedFullHistoryFamilyBits.prefixLength P key) := rfl

theorem creating_coordinate_snapshot (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) :
    (IntegralMixedFullHistoryFamilyBits.creatingCommand P D key).coordinate =
      commandCoordinate P D (pairFst key) (IntegralMixedFullHistoryFamilyBits.prefixLength P key) := rfl

theorem producerKey_prefix (P : Parameters) (q : List Bool) :
    IntegralMixedFullHistoryFamilyBits.prefixLength P
      (IntegralMixedFullHistoryFamilyBits.producerKey (packet P q)) = producerBirth P q := by
  simp only [IntegralMixedFullHistoryFamilyBits.prefixLength, IntegralMixedFullHistoryFamilyBits.producerKey,
    IntegralMixedOldBankCofactorBits.producerBirth, packet, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact min_eq_left (producerBirth_bound P q)

theorem routing_context (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    (IntegralMixedFullHistoryFamilyBits.routing P D).context (packet P q) =
      commandContext P D (RankedHistoryTask.root q) (producerBirth P q) := by
  change (IntegralMixedFullHistoryFamilyBits.creatingCommand P D _).context = _
  rw [creating_context_snapshot, producerKey_prefix]
  simp only [IntegralMixedFullHistoryFamilyBits.producerKey, packet, pairFst_pair]

theorem routing_coordinate (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    (IntegralMixedFullHistoryFamilyBits.routing P D).coordinate (packet P q) =
      commandCoordinate P D (RankedHistoryTask.root q) (producerBirth P q) := by
  change (IntegralMixedFullHistoryFamilyBits.creatingCommand P D _).coordinate = _
  rw [creating_coordinate_snapshot, producerKey_prefix]
  simp only [IntegralMixedFullHistoryFamilyBits.producerKey, packet, pairFst_pair]

theorem child_context (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    get P .slot15 (writer P (IntegralMixedFullHistoryFamilyBits.routing P D) q) =
      (IntegralMixedFullHistoryFamilyBits.creatingCommand P D
        (IntegralMixedVirtualTaskBits.saved P (writer P (IntegralMixedFullHistoryFamilyBits.routing P D) q))).context := by
  rw [writer_context P _ q (by simpa only [packet, pairFst_pair] using
    IntegralMixedFullHistoryFamilyBits.routing_context_bound P D (packet P q))]
  rw [routing_context, creating_context_snapshot, IntegralMixedFullHistoryFamilyBits.saved_root,
    IntegralMixedFullHistoryFamilyBits.saved_prefix, writer_root, writer_birth]

theorem child_coordinate (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    get P .slot13 (writer P (IntegralMixedFullHistoryFamilyBits.routing P D) q) =
      (IntegralMixedFullHistoryFamilyBits.creatingCommand P D
        (IntegralMixedVirtualTaskBits.saved P (writer P (IntegralMixedFullHistoryFamilyBits.routing P D) q))).coordinate := by
  rw [writer_coordinate P _ q (by simpa only [packet, pairFst_pair] using
    IntegralMixedFullHistoryFamilyBits.routing_coordinate_bound P D (packet P q))]
  rw [routing_coordinate, creating_coordinate_snapshot, IntegralMixedFullHistoryFamilyBits.saved_root,
    IntegralMixedFullHistoryFamilyBits.saved_prefix, writer_root, writer_birth]

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullHistoryFamilyBits.Metadata P D) :=
  IntegralMixedNativeOldHeightBits.machine P a D (IntegralMixedFullHistoryFamilyBits.routing P D)
    (IntegralMixedFullHistoryFamilyBits.routingAccess P D h)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullHistoryFamilyBits.Metadata P D) (reply : List Bool → List Bool)
    (he : ∀ q, IntegralMixedNativeOldHeightBits.selected P q = true →
      PassRepliesAt P D (IntegralMixedFullHistoryFamilyBits.routing P D) reply q) :
    NativeControllerBranch.Correct (machine P a D h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedNativeOldHeightBits.correct P a D (IntegralMixedFullHistoryFamilyBits.routing P D)
    (IntegralMixedFullHistoryFamilyBits.routingAccess P D h) reply he

end LeanCanny.Algebra.IntegralMixedFullOldHeightBits
