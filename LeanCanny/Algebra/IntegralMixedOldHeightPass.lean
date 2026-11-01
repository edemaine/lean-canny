/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOldHeightModel
public import LeanCanny.Algebra.IntegralMixedOldHeightQueryFields
/-! # Charged cofactor and companion pass for actual mixed old heights -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def companionInteger (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (R : Routing) (q : List Bool) : ℤ :=
  (IntegralMixedFullHistoryCompanionBits.source P D).matrix
    (IntegralMixedVirtualTaskBits.saved P (writer P R q))
    (IntegralMixedFullHistoryCompanionBits.row P D (writer P R q))
    (IntegralMixedFullHistoryCompanionBits.col P D (writer P R q))

noncomputable def passCount (P : Parameters) (q : List Bool) := if request P q then birth P q + 1 else 0

theorem passCount_unary (P : Parameters) (a : Access P) : UnaryFn (passCount P) :=
  UnaryFn.ite (request_FP P a) ((birth_unary P a).add (UnaryFn.const 1)) (UnaryFn.const 0)

noncomputable def passScale (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (R : Routing) (q : List Bool) (j : ℕ) : ℤ :=
  if hj : j < (bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q) then
    (state P D q).bank.denominator ⟨j, hj⟩
  else companionInteger P D R q

noncomputable def passScalars (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing) : CommonHeightBits.Scalars where
  count := passCount P
  modulus := modulus P
  modulus_ne_zero := modulus_ne_zero P
  scale := passScale P D R
  selected := index P

theorem passControls (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing) :
    CommonHeightRecursivePass.Controls (passScalars P D R) :=
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

theorem passTask_leading (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing)
    (q : List Bool) (b j : ℕ) (hj : j < birth P q) :
    passTask P R (pair q (pair (BinaryNatCode.encode b) (BinaryNatCode.encode j))) =
      IntegralMixedOldBankCofactorBits.writer P R (IntegralMixedOldBankCofactorBits.packet P (bankFamily P D) q j) := by
  simp only [passTask, IntegralMixedOldBankCofactorBits.retainedIndex, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, hj, ite_true, leadingPacket]
  rw [IntegralMixedOldBankCofactorBits.packet, IntegralMixedOldBankCofactorBits.count_eq P (bankFamily P D)
    (IntegralMixedFullHistoryFamilyBits.geometry P D) q]
  rfl

theorem passTask_companion (P : Parameters) (R : Routing) (q : List Bool) (b : ℕ) :
    passTask P R (pair q (pair (BinaryNatCode.encode b) (BinaryNatCode.encode (birth P q)))) = writer P R q := by
  simp only [passTask, IntegralMixedOldBankCofactorBits.retainedIndex, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, lt_self_iff_false, ite_false]

noncomputable def passProgram (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing) :=
  CommonHeightRecursivePass.program (passScalars P D R) (passTask P R)

theorem passCertificates (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (R : Routing) (hr : RoutingAccess R) :
    (passProgram P D R).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  CommonHeightRecursivePass.certificates _ (passControls P a D R) _ (passTask_FP P a R hr)

structure PassRepliesAt (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) : Prop where
  leading : request P q → IntegralMixedOldBankCofactorBits.RepliesAt P (bankFamily P D) R reply q
  companion : request P q → reply (writer P R q) = IntegralMixedFullHistoryCompanionBits.value P D (writer P R q)

theorem passReplies_scale (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (he : PassRepliesAt P D R reply q) :
    ∀ j < (passScalars P D R).count q,
      reply (passTask P R (pair q (pair (BinaryNatCode.encode ((passScalars P D R).count q - 1 - j)) (BinaryNatCode.encode j)))) =
        residueBits ((passScalars P D R).scale q j : ZMod ((passScalars P D R).modulus q)) := by
  intro j hj
  change j < passCount P q at hj
  have HQ : request P q := by
    by_contra hn
    have H : j < 0 := by simpa only [passCount, ite_eq_right hn] using hj
    exact Nat.not_lt_zero j H
  have HJ : j < birth P q + 1 := by simpa only [passCount, ite_eq_left HQ] using hj
  by_cases HB : j < birth P q
  · rw [passTask_leading P D R q _ j HB]
    have HI : j < (bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q) := HB.trans_eq (bank_birth P D q).symm
    change _ = residueBits (passScale P D R q j : ZMod (modulus P q))
    rw [passScale, dite_eq_left HI]
    exact he.leading HQ ⟨j, HI⟩
  · have HM : j = birth P q := by omega
    subst j
    rw [passTask_companion]
    change _ = residueBits (passScale P D R q (birth P q) : ZMod (modulus P q))
    rw [passScale, dite_eq_right (by rw [bank_birth]; exact Nat.lt_irrefl _)]
    exact (he.companion HQ).trans (congrArg (fun m => residueBits (companionInteger P D R q : ZMod m)) (writer_modulus P R q))

theorem pass_value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (he : PassRepliesAt P D R reply q) :
    (passProgram P D R).value reply q = residueBits ((passScalars P D R).cofactor q : ZMod (modulus P q)) :=
  CommonHeightRecursivePass.value_eq _ _ _ _ (passReplies_scale P D R reply q he)

end LeanCanny.Algebra.IntegralMixedOldHeightBits
