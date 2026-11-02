/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightRootSnapshot
public import LeanCanny.Algebra.IntegralMixedOldHeightQueryFields
/-! # Charged cofactor and companion pass for actual mixed old heights -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
open IntegralMixedOldHeightBits (request request_FP birth_unary index index_unary writer writer_FP writer_modulus)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def passCount (P : Parameters) (q : List Bool) := if request P q then birth P q + 1 else 0

theorem passCount_unary (P : Parameters) (a : Access P) : UnaryFn (passCount P) :=
  UnaryFn.ite (request_FP P a) ((birth_unary P a).add (UnaryFn.const 1)) (UnaryFn.const 0)

noncomputable def passScale (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (R : Routing) (q : List Bool) (j : ℕ) : ℤ :=
  if hj : j < (bankFamily P D F).birth (IntegralMixedVirtualTaskBits.saved P q) then
    (state P D F q).bank.denominator ⟨j, hj⟩
  else companionInteger P D F R q

attribute [local irreducible] passScale companionInteger modulus

noncomputable def passScalars (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing) : CommonHeightBits.Scalars where
  count := passCount P
  modulus := modulus P
  modulus_ne_zero := modulus_ne_zero P
  scale := passScale P D F R
  selected := index P

theorem passControls (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing) :
    CommonHeightRecursivePass.Controls (passScalars P D F R) :=
  ⟨passCount_unary P a, modulus_binary P a, BinaryFn.ofUnary (index_unary P a)⟩

def leadingPacket (P : Parameters) (z : List Bool) :=
  pair (pairFst z) (pair (BinaryNatCode.encode (birth P (pairFst z) - 1 - IntegralMixedOldBankCofactorBits.retainedIndex z))
    (BinaryNatCode.encode (IntegralMixedOldBankCofactorBits.retainedIndex z)))

theorem leadingPacket_FP (P : Parameters) (a : Access P) : leadingPacket P ∈ FP := by
  have HB : BinaryFn (fun z => birth P (pairFst z)) := (BinaryFn.ofUnary (birth_unary P a)).comp pairFst_mem_FP
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair
    ((HB.sub (BinaryFn.const 1)).sub IntegralMixedOldBankCofactorBits.retainedIndex_binary).bits_mem_FP
    IntegralMixedOldBankCofactorBits.retainedIndex_binary.bits_mem_FP)

def passTask (P : Parameters) (R : Routing) (z : List Bool) :=
  if IntegralMixedOldBankCofactorBits.retainedIndex z < birth P (pairFst z) then
    IntegralMixedOldBankCofactorBits.writer P R (leadingPacket P z)
  else writer P R (pairFst z)

theorem passTask_FP (P : Parameters) (a : Access P) (R : Routing) (hr : RoutingAccess R) : passTask P R ∈ FP :=
  (IntegralMixedOldBankCofactorBits.retainedIndex_binary.lt ((BinaryFn.ofUnary (birth_unary P a)).comp pairFst_mem_FP)).ite_mem_FP
    (mem_FP_comp (leadingPacket_FP P a) (IntegralMixedOldBankCofactorBits.writer_FP P a R hr))
    (mem_FP_comp pairFst_mem_FP (writer_FP P a R hr))

theorem passTask_leading (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing)
    (q : List Bool) (b j : ℕ) (hj : j < birth P q) :
    passTask P R (pair q (pair (BinaryNatCode.encode b) (BinaryNatCode.encode j))) =
      IntegralMixedOldBankCofactorBits.writer P R (IntegralMixedOldBankCofactorBits.packet P (bankFamily P D F) q j) := by
  simp only [passTask, IntegralMixedOldBankCofactorBits.retainedIndex, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, hj, ite_true, leadingPacket]
  rw [IntegralMixedOldBankCofactorBits.packet, IntegralMixedOldBankCofactorBits.count_eq P (bankFamily P D F)
    (IntegralMixedFramedHistoryFamilyBits.geometry P D F) q]
  rfl

theorem passTask_companion (P : Parameters) (R : Routing) (q : List Bool) (b : ℕ) :
    passTask P R (pair q (pair (BinaryNatCode.encode b) (BinaryNatCode.encode (birth P q)))) = writer P R q := by
  simp only [passTask, IntegralMixedOldBankCofactorBits.retainedIndex, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, lt_self_iff_false, ite_false]

noncomputable def passProgram (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing) :=
  CommonHeightRecursivePass.program (passScalars P D F R) (passTask P R)

theorem passCertificates (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (R : Routing) (hr : RoutingAccess R) :
    (passProgram P D F R).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  CommonHeightRecursivePass.certificates (passScalars P D F R) (passControls P a D F R) (passTask P R) (passTask_FP P a R hr)

structure PassRepliesAt (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) : Prop where
  leading : request P q → IntegralMixedOldBankCofactorBits.RepliesAt P (bankFamily P D F) R reply q
  companion : request P q → reply (writer P R q) = IntegralMixedFramedCompanionBits.value P D F (writer P R q)

theorem passReplies_scale (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (he : PassRepliesAt P D F R reply q) :
    ∀ j < (passScalars P D F R).count q,
      reply (passTask P R (pair q (pair (BinaryNatCode.encode ((passScalars P D F R).count q - 1 - j)) (BinaryNatCode.encode j)))) =
        residueBits ((passScalars P D F R).scale q j : ZMod ((passScalars P D F R).modulus q)) := by
  intro j hj
  change j < passCount P q at hj
  have HQ : request P q := by
    by_contra hn
    have H : j < 0 := by simpa only [passCount, ite_eq_right hn] using hj
    exact Nat.not_lt_zero j H
  have HJ : j < birth P q + 1 := by simpa only [passCount, ite_eq_left HQ] using hj
  by_cases HB : j < birth P q
  · rw [passTask_leading P D F R q _ j HB]
    have HI : j < (bankFamily P D F).birth (IntegralMixedVirtualTaskBits.saved P q) := HB.trans_eq (bank_birth P D F q).symm
    change _ = residueBits (passScale P D F R q j : ZMod (modulus P q))
    rw [passScale, dite_eq_left HI]
    exact he.leading HQ ⟨j, HI⟩
  · have HM : j = birth P q := by omega
    subst j
    rw [passTask_companion]
    change _ = residueBits (passScale P D F R q (birth P q) : ZMod (modulus P q))
    rw [passScale, dite_eq_right (by rw [bank_birth]; exact Nat.lt_irrefl _)]
    refine (he.companion HQ).trans ?_
    simpa only [sourceEntry_value, companionInteger] using
      congrArg (fun m => residueBits (companionInteger P D F R q : ZMod m)) (writer_modulus P R q)

theorem pass_value (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (he : PassRepliesAt P D F R reply q) :
    (passProgram P D F R).value reply q = residueBits ((passScalars P D F R).cofactor q : ZMod (modulus P q)) :=
  CommonHeightRecursivePass.value_eq (passScalars P D F R) (passTask P R) reply q (passReplies_scale P D F R reply q he)

end LeanCanny.Algebra.IntegralMixedFramedOldHeightBits
