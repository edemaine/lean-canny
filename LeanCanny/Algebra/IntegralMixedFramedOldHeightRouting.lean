/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNativeOldHeight
public import LeanCanny.Algebra.IntegralMixedFramedProducerRouting
/-! # Native earlier-companion labels of framed retained-height requests -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan instruction prefixLength)
open IntegralMixedOldHeightBits (packet producerBirth producerBirth_bound writer writer_context writer_coordinate writer_root writer_birth)
open IntegralMixedFramedProducerActualBits (contextSnapshot coordinateSnapshot instruction_context_snapshot instruction_coordinate_snapshot framed_saved_prefix)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem producerKey_prefix (P : Parameters) (q : List Bool) :
    prefixLength P (IntegralMixedFullHistoryFamilyBits.producerKey (packet P q)) = producerBirth P q := by
  simp only [prefixLength, IntegralMixedFullHistoryFamilyBits.prefixLength, IntegralMixedFullHistoryFamilyBits.producerKey,
    IntegralMixedOldBankCofactorBits.producerBirth, packet, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact min_eq_left (producerBirth_bound P q)

theorem routing_context (P : Parameters) (D : Plan P) (q : List Bool) :
    (IntegralMixedFramedHeaderBits.routing P D).context (packet P q) = contextSnapshot P D (RankedHistoryTask.root q) (producerBirth P q) := by
  change (instruction P D (IntegralMixedFullHistoryFamilyBits.producerKey (packet P q))).command.context = _
  rw [instruction_context_snapshot, producerKey_prefix]
  simp only [IntegralMixedFullHistoryFamilyBits.producerKey, packet, pairFst_pair]

theorem routing_coordinate (P : Parameters) (D : Plan P) (q : List Bool) :
    (IntegralMixedFramedHeaderBits.routing P D).coordinate (packet P q) = coordinateSnapshot P D (RankedHistoryTask.root q) (producerBirth P q) := by
  change (instruction P D (IntegralMixedFullHistoryFamilyBits.producerKey (packet P q))).command.coordinate = _
  rw [instruction_coordinate_snapshot, producerKey_prefix]
  simp only [IntegralMixedFullHistoryFamilyBits.producerKey, packet, pairFst_pair]

theorem child_context (P : Parameters) (D : Plan P) (q : List Bool) :
    get P .slot15 (writer P (IntegralMixedFramedHeaderBits.routing P D) q) =
      (instruction P D (IntegralMixedVirtualTaskBits.saved P (writer P (IntegralMixedFramedHeaderBits.routing P D) q))).command.context := by
  rw [writer_context P _ q (by simpa only [packet, pairFst_pair] using IntegralMixedFramedHeaderBits.routing_context_bound P D (packet P q))]
  rw [routing_context, instruction_context_snapshot, IntegralMixedFullHistoryFamilyBits.saved_root,
    framed_saved_prefix, writer_root, writer_birth]

theorem child_coordinate (P : Parameters) (D : Plan P) (q : List Bool) :
    get P .slot13 (writer P (IntegralMixedFramedHeaderBits.routing P D) q) =
      (instruction P D (IntegralMixedVirtualTaskBits.saved P (writer P (IntegralMixedFramedHeaderBits.routing P D) q))).command.coordinate := by
  rw [writer_coordinate P _ q (by simpa only [packet, pairFst_pair] using IntegralMixedFramedHeaderBits.routing_coordinate_bound P D (packet P q))]
  rw [routing_coordinate, instruction_coordinate_snapshot, IntegralMixedFullHistoryFamilyBits.saved_root,
    framed_saved_prefix, writer_root, writer_birth]

noncomputable def machine (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D H T) :=
  IntegralMixedFramedNativeOldHeightBits.machine P a D H (IntegralMixedFramedHeaderBits.routing P D)
    (IntegralMixedFramedHeaderBits.routingAccess P a D H T ht hr)

theorem correct (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (ht : IntegralMixedHeaderTablesBits.Access T)
    (hr : IntegralMixedFramedHeaderBits.Represents P D H T) (answer : List Bool → List Bool)
    (he : ∀ q, IntegralMixedFramedNativeOldHeightBits.selected P q = true → PassRepliesAt P D H (IntegralMixedFramedHeaderBits.routing P D) answer q) :
    NativeControllerBranch.Correct (machine P a D H T ht hr) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedFramedNativeOldHeightBits.correct P a D H (IntegralMixedFramedHeaderBits.routing P D)
    (IntegralMixedFramedHeaderBits.routingAccess P a D H T ht hr) answer he
end LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
