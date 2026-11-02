/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedProducerRouting
/-! # Current native producers provide every actual framed bank denominator -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedProducerActualBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength)
open IntegralMixedOldBankCofactorBits
open scoped Classical

private theorem child_leading (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) (i : Fin (count P (IntegralMixedFramedHistoryFamilyBits.family P D H) q)) :
    IntegralMixedFramedCompanionBits.leading P D H
      (IntegralMixedVirtualTaskBits.saved P (writer P (IntegralMixedFramedHeaderBits.routing P D)
        (packet P (IntegralMixedFramedHistoryFamilyBits.family P D H) q i.val)))=
      ((IntegralMixedFramedHistoryFamilyBits.family P D H).state (IntegralMixedVirtualTaskBits.saved P q)).bank.denominator i := by
  let F := IntegralMixedFramedHistoryFamilyBits.family P D H
  let R := IntegralMixedFramedHeaderBits.routing P D
  let key := IntegralMixedVirtualTaskBits.saved P q
  let g := IntegralMixedFramedHistoryFamilyBits.geometry P D H
  have HC : R.context (packet P F q i.val)≤numericCap P (RankedHistoryTask.root q) := by
    simpa only [packet,pairFst_pair] using IntegralMixedFramedHeaderBits.routing_context_bound P D (packet P F q i.val)
  have HE := writer_packet_saved P F g R q i.val i.isLt HC
  have HK : IntegralMixedVirtualTaskBits.saved P (writer P R (packet P F q i.val))=
      IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst key) (prefixLength P key-1-i.val)
        (BinaryNatCode.encode (R.context (packet P F q i.val))) := by
    rw [HE]
    unfold IntegralMixedFramedHistoryFamilyBits.keyAt
    rw [show pairFst key=RankedHistoryTask.root q from IntegralMixedFullHistoryFamilyBits.saved_root P q]
    exact congrArg (fun m : ℕ => pair (RankedHistoryTask.root q)
      (pair (BinaryNatCode.encode (m-1-i.val)) (BinaryNatCode.encode (R.context (packet P F q i.val)))))
      (show count P F q=prefixLength P key from IntegralMixedFramedHistoryFamilyBits.family_birth P D H key)
  have HL := IntegralMixedFramedHistoryFamilyBits.retained_leading_key P D H key ⟨i.val,i.isLt⟩
    (BinaryNatCode.encode (R.context (packet P F q i.val)))
  change _=IntegralMixedFramedCompanionBits.leading P D H
    (IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst key) (prefixLength P key-1-i.val)
      (BinaryNatCode.encode (R.context (packet P F q i.val)))) at HL
  rw [HK]
  exact HL.symm

theorem bank_replies (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (answer : List Bool → List Bool) (own : Matches P D H answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) :
    RepliesAt P (IntegralMixedFramedHistoryFamilyBits.family P D H) (IntegralMixedFramedHeaderBits.routing P D) answer q := by
  let F := IntegralMixedFramedHistoryFamilyBits.family P D H
  let R := IntegralMixedFramedHeaderBits.routing P D
  let g := IntegralMixedFramedHistoryFamilyBits.geometry P D H
  intro i
  let z := packet P F q i.val
  let c := writer P R z
  have hb : producerBirth z≤birthCap P (RankedHistoryTask.root (pairFst z)) := by
    simp only [z,producerBirth,packet,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    have HE := count_eq P F g q
    have HT : birth P q≤birthCap P (RankedHistoryTask.root q) := min_le_right _ _
    omega
  have hx := leading_query_context P D z hb
  have hc : IntegralMixedVirtualCaps.valid P c := by
    unfold IntegralMixedVirtualCaps.valid
    rw [writer_root,show pairFst z=q from pairFst_pair _ _,writer_packet_birth P F g R q i.val i.isLt]
    have HE := count_eq P F g q
    unfold IntegralMixedVirtualCaps.valid at hv
    have HI := i.isLt
    omega
  have HV := (own.leading c hc (writer_routine P R z)
    (hx.trans_le (IntegralMixedFullHistoryScript.Command.context_le _)) (writer_phase P R z)).trans
      (leading_actual P D H c hx)
  have HM : modulus P c=modulus P q := by
    simpa only [c,z,packet,pairFst_pair] using writer_modulus P R z
  exact HV.trans (congrArg₂ (fun (v : ℤ) (m : ℕ) => residueBits (v : ZMod m)) (child_leading P D H q i) HM)

end LeanCanny.Algebra.IntegralMixedFramedProducerActualBits
