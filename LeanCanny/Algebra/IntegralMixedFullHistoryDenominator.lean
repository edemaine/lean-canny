/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHistoryFamily
public import LeanCanny.Algebra.IntegralMixedNativeCommonDenominator
/-! # Actual full-history provenance closes the scalar denominator controller

The sole recursive reply contract names the literal creating command and
its actual older interpreted prefix. Its retained denominator identity is
proved by the full-history origin theorem, including normalized raw cuts.
Original-command metadata and original integer affine scale-cell reads are
separate input-codec obligations; there is no state or leading evaluator.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullHistoryDenominatorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedFullHistoryFamilyBits
set_option backward.isDefEq.respectTransparency false

noncomputable def producerLeading (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) (i : Fin ((family P D).birth key)) : ℤ :=
  leading (birthState (initial P D (pairFst key)) (commands P D key)
    (((family P D).birth_bound key).trans (Nat.le_succ _)) i)
    (older_bound (commands P D key) (((family P D).birth_bound key).trans (Nat.le_succ _)) i)
    (chosen (commands P D key) i)

theorem retained_leading (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (key : List Bool) (i : Fin ((family P D).birth key)) :
    ((family P D).state key).bank.denominator i = producerLeading P D key i := origin_denominator P D key i

abbrev ProducerRepliesAt (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ i : Fin (IntegralMixedOldBankCofactorBits.count P (family P D) q),
    reply (IntegralMixedOldBankCofactorBits.writer P (routing P D)
      (IntegralMixedOldBankCofactorBits.packet P (family P D) q i.val)) =
      residueBits (producerLeading P D (IntegralMixedVirtualTaskBits.saved P q) i : ZMod (modulus P q))

theorem replies (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (reply : List Bool → List Bool) (q : List Bool)
    (he : ProducerRepliesAt P D reply q) : IntegralMixedOldBankCofactorBits.RepliesAt P (family P D) (routing P D) reply q := by
  intro i
  exact (he i).trans (congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
    (retained_leading P D (IntegralMixedVirtualTaskBits.saved P q) i).symm)

theorem producer_frame (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (i : ℕ)
    (hi : i < IntegralMixedOldBankCofactorBits.count P (family P D) q) :
    IntegralMixedRoutineTaskBits.Frame P q (IntegralMixedOldBankCofactorBits.writer P (routing P D)
      (IntegralMixedOldBankCofactorBits.packet P (family P D) q i)) :=
  IntegralMixedOldBankCofactorBits.writer_packet_frame P (family P D) (geometry P D) (routing P D) q i hi

theorem producer_key (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (i : ℕ)
    (hi : i < IntegralMixedOldBankCofactorBits.count P (family P D) q) :
    IntegralMixedVirtualTaskBits.saved P
      (IntegralMixedOldBankCofactorBits.writer P (routing P D) (IntegralMixedOldBankCofactorBits.packet P (family P D) q i)) =
      pair (RankedHistoryTask.root q)
        (pair (BinaryNatCode.encode (IntegralMixedOldBankCofactorBits.count P (family P D) q - 1 - i))
          (BinaryNatCode.encode ((routing P D).context (IntegralMixedOldBankCofactorBits.packet P (family P D) q i)))) := by
  apply IntegralMixedOldBankCofactorBits.writer_packet_saved P (family P D) (geometry P D) (routing P D) q i hi
  simpa only [IntegralMixedOldBankCofactorBits.packet, pairFst_pair] using
    routing_context_bound P D (IntegralMixedOldBankCofactorBits.packet P (family P D) q i)

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Metadata P D)
    (hp : IntegralMixedNativeCommonDenominatorBits.Primitive P (family P D)) :=
  IntegralMixedNativeCommonDenominatorBits.machine P a (family P D) (inputMetadata P a D h) (geometry P D)
    (routing P D) (routingAccess P D h) hp

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Metadata P D)
    (hp : IntegralMixedNativeCommonDenominatorBits.Primitive P (family P D))
    (reply : List Bool → List Bool)
    (he : ∀ q, IntegralMixedNativeCommonDenominatorBits.selected P q = true → ProducerRepliesAt P D reply q) :
    NativeControllerBranch.Correct (machine P a D h hp) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedNativeCommonDenominatorBits.correct P a (family P D) (inputMetadata P a D h) (geometry P D)
    (routing P D) (routingAccess P D h) hp reply (fun q hq => replies P D reply q (he q hq))
end LeanCanny.Algebra.IntegralMixedFullHistoryDenominatorBits
