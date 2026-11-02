/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateOutside
public import LeanCanny.Algebra.IntegralMixedOldHeightCurrentProducers
/-! # Literal current producers close every bank factor of a limit coefficient -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullLimitCoordinate
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical

theorem bank_replies (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (answer : List Bool → List Bool) (own : IntegralMixedProducerActualBits.Matches P D answer)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralMixedOldBankCofactorBits.RepliesAt P (IntegralMixedFullHistoryFamilyBits.family P D)
      (IntegralMixedFullHistoryFamilyBits.routing P D) answer q := by
  let F := IntegralMixedOldHeightBits.bankFamily P D
  let R := IntegralMixedFullHistoryFamilyBits.routing P D
  let g := IntegralMixedFullHistoryFamilyBits.geometry P D
  intro i
  let z := IntegralMixedOldBankCofactorBits.packet P F q i.val
  let c := IntegralMixedOldBankCofactorBits.writer P R z
  have hb : IntegralMixedOldBankCofactorBits.producerBirth z ≤ birthCap P (RankedHistoryTask.root (pairFst z)) := by
    simp only [z, IntegralMixedOldBankCofactorBits.producerBirth, IntegralMixedOldBankCofactorBits.packet,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have HE := IntegralMixedOldBankCofactorBits.count_eq P F g q
    have HT : birth P q≤birthCap P (RankedHistoryTask.root q) := min_le_right _ _
    omega
  have hx := IntegralMixedProducerActualBits.leading_query_context P D z hb
  have hc : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid
    rw [IntegralMixedOldBankCofactorBits.writer_root, show pairFst z=q from pairFst_pair _ _,
      IntegralMixedOldBankCofactorBits.writer_packet_birth P F g R q i.val i.isLt]
    have HE := IntegralMixedOldBankCofactorBits.count_eq P F g q
    unfold IntegralMixedVirtualCaps.valid at hv
    have HI := i.isLt
    omega
  have H := (own.leading c hc (IntegralMixedOldBankCofactorBits.writer_routine P R z)
    (hx.trans_le (IntegralMixedFullHistoryScript.Command.context_le _))
    (IntegralMixedOldBankCofactorBits.writer_phase P R z)).trans
      (IntegralMixedProducerActualBits.leading_actual P D c hx)
  have HL := IntegralMixedOldBankLeadingBits.child_leading P D R q i
  have HM : modulus P c=modulus P q := by
    simpa only [c, z, IntegralMixedOldBankCofactorBits.packet, pairFst_pair] using
      IntegralMixedOldBankCofactorBits.writer_modulus P R z
  exact H.trans (congrArg₂ (fun (v : ℤ) (m : ℕ) => residueBits (v : ZMod m)) HL HM)

noncomputable def branch (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullHistoryFamilyBits.Metadata P D) :=
  IntegralMixedLimitCoordinateNative.branch P a (IntegralMixedFullHistoryFamilyBits.family P D)
    (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h)
    (IntegralMixedFullHistoryFamilyBits.routing P D) (IntegralMixedFullHistoryFamilyBits.routingAccess P D h)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullHistoryFamilyBits.Metadata P D) (answer : List Bool → List Bool)
    (producer : IntegralMixedProducerActualBits.Matches P D answer)
    (critical : IntegralMixedVirtualContextComponentBits.Matches P (IntegralMixedFullHistoryFamilyBits.family P D) answer) :
    Correct (branch P a D h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedLimitCoordinateNative.branch_correct P a (IntegralMixedFullHistoryFamilyBits.family P D)
    (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h) (IntegralMixedFullHistoryFamilyBits.geometry P D)
    (IntegralMixedFullHistoryFamilyBits.routing P D) (IntegralMixedFullHistoryFamilyBits.routingAccess P D h)
    answer critical (fun q hs => bank_replies P D answer producer q hs.1)

end LeanCanny.Algebra.IntegralMixedFullLimitCoordinate
