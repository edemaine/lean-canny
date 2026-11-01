/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNativeHeightActual
public import LeanCanny.Algebra.IntegralMixedOldHeightCurrentProducers
/-! # Current producer and retained-height matches close native scalar-height requests -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightCurrentBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedOldHeightBits (bankFamily)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Matches (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (answer : List Bool → List Bool) : Prop where
  height : ∀ q, IntegralMixedNativeOldHeightBits.selected P q = true →
    (1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) → answer q = IntegralMixedOldHeightBits.value P D q

theorem leading_replies (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (answer : List Bool → List Bool) (hm : IntegralMixedProducerActualBits.Matches P D answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) :
    IntegralMixedOldBankCofactorBits.RepliesAt P (bankFamily P D) (IntegralMixedFullHistoryFamilyBits.routing P D) answer q := by
  let R := IntegralMixedFullHistoryFamilyBits.routing P D
  let F := bankFamily P D
  let g := IntegralMixedFullHistoryFamilyBits.geometry P D
  intro i
  let z := IntegralMixedOldBankCofactorBits.packet P F q i.val
  let c := IntegralMixedOldBankCofactorBits.writer P R z
  have hb : IntegralMixedOldBankCofactorBits.producerBirth z ≤ birthCap P (RankedHistoryTask.root (pairFst z)) := by
    simp only [z, IntegralMixedOldBankCofactorBits.producerBirth, IntegralMixedOldBankCofactorBits.packet,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have HE := IntegralMixedOldBankCofactorBits.count_eq P F g q
    have HT : birth P q ≤ birthCap P (RankedHistoryTask.root q) := min_le_right _ _
    omega
  have hx := IntegralMixedProducerActualBits.leading_query_context P D z hb
  have hc : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid
    rw [IntegralMixedOldBankCofactorBits.writer_root, show pairFst z = q from pairFst_pair _ _,
      IntegralMixedOldBankCofactorBits.writer_packet_birth P F g R q i.val i.isLt]
    have HE := IntegralMixedOldBankCofactorBits.count_eq P F g q
    unfold IntegralMixedVirtualCaps.valid at hv
    omega
  have H := (hm.leading c hc (IntegralMixedOldBankCofactorBits.writer_routine P R z)
      (hx.trans_le (IntegralMixedFullHistoryScript.Command.context_le _))
      (IntegralMixedOldBankCofactorBits.writer_phase P R z)).trans (IntegralMixedProducerActualBits.leading_actual P D c hx)
  have HL := IntegralMixedOldBankLeadingBits.child_leading P D R q i
  have HM : modulus P c = modulus P q := by
    simpa only [c, z, IntegralMixedOldBankCofactorBits.packet, pairFst_pair] using IntegralMixedOldBankCofactorBits.writer_modulus P R z
  exact H.trans (congrArg₂ (fun (s : ℤ) (m : ℕ) => residueBits (s : ZMod m)) HL HM)

theorem replies (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (answer : List Bool → List Bool) (hp : IntegralMixedProducerActualBits.Matches P D answer) (hm : Matches P D answer)
    (q : List Bool) (hq : IntegralMixedNativeHeightBits.selected P q = true) :
    IntegralMixedHeightTablePassBits.RepliesAt P D (IntegralMixedFullHistoryFamilyBits.routing P D) answer q := by
  rcases (IntegralMixedNativeHeightBits.selected_iff P q).mp hq with ⟨HV, _HR, _HP, HX⟩
  refine ⟨leading_replies P D answer hp q HV, ?_⟩
  intro i _
  have HC := IntegralMixedHeightTableQueryBits.writer_selected P q i HV
  have HE : get P .slot15 (IntegralMixedHeightTableQueryBits.writer P (pair q (BinaryNatCode.encode i))) = get P .slot15 q := by
    rw [IntegralMixedHeightTableQueryBits.writer_get]
    rfl
  exact hm.height _ HC (by rwa [HE])

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullHistoryFamilyBits.Metadata P D) (hc : IntegralMixedHeightCellsBits.Primitive P D)
    (answer : List Bool → List Bool) (hp : IntegralMixedProducerActualBits.Matches P D answer) (hm : Matches P D answer) :
    NativeControllerBranch.Correct (IntegralMixedNativeHeightBits.machine P a D (IntegralMixedFullHistoryFamilyBits.routing P D)
      (IntegralMixedFullHistoryFamilyBits.routingAccess P D h) hc) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedNativeHeightBits.correct P a D _ (IntegralMixedFullHistoryFamilyBits.routingAccess P D h) hc answer
    (fun q hq => replies P D answer hp hm q hq)

end LeanCanny.Algebra.IntegralMixedHeightCurrentBits
