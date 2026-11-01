/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightTableQuery
public import LeanCanny.Computation.NativeFixedWidthVectorPassBounds
/-! # Charged tables of old-bank leadings and cleared affine references -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightTablePassBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
open IntegralMixedOldHeightBits (bankFamily)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def count (P : Parameters) (q : List Bool) := 2 * birth P q
def width (P : Parameters) (q : List Bool) := (modulus P q).size

theorem count_unary (P : Parameters) (a : Access P) : UnaryFn (count P) :=
  (UnaryFn.const 2).mul (IntegralMixedOldHeightBits.birth_unary P a)
theorem width_unary (P : Parameters) (a : Access P) : UnaryFn (width P) :=
  (UnaryFn.length (modulus_binary P a).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

def leadingPacket (P : Parameters) (p : List Bool) := pair (pairFst p)
  (pair (BinaryNatCode.encode (birth P (pairFst p) - 1 - Nat.fromBitsLE (pairSnd p))) (pairSnd p))
theorem leadingPacket_FP (P : Parameters) (a : Access P) : leadingPacket P ∈ FP := by
  have HB : BinaryFn (fun p => birth P (pairFst p)) := (BinaryFn.ofUnary (IntegralMixedOldHeightBits.birth_unary P a)).comp pairFst_mem_FP
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair
    ((HB.sub (BinaryFn.const 1)).sub (BinaryFn.fromBits pairSnd_mem_FP)).bits_mem_FP pairSnd_mem_FP)

def heightPacket (P : Parameters) (p : List Bool) := pair (pairFst p)
  (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd p) - birth P (pairFst p)))
theorem heightPacket_FP (P : Parameters) (a : Access P) : heightPacket P ∈ FP := by
  have HB : BinaryFn (fun p => birth P (pairFst p)) := (BinaryFn.ofUnary (IntegralMixedOldHeightBits.birth_unary P a)).comp pairFst_mem_FP
  exact mem_FP_pair pairFst_mem_FP ((BinaryFn.fromBits pairSnd_mem_FP).sub HB).bits_mem_FP

def task (P : Parameters) (R : Routing) (p : List Bool) :=
  if Nat.fromBitsLE (pairSnd p) < birth P (pairFst p) then IntegralMixedOldBankCofactorBits.writer P R (leadingPacket P p)
  else IntegralMixedHeightTableQueryBits.writer P (heightPacket P p)
theorem task_FP (P : Parameters) (a : Access P) (R : Routing) (hr : RoutingAccess R) : task P R ∈ FP := by
  have HB : BinaryFn (fun p => birth P (pairFst p)) := (BinaryFn.ofUnary (IntegralMixedOldHeightBits.birth_unary P a)).comp pairFst_mem_FP
  exact ((BinaryFn.fromBits pairSnd_mem_FP).lt HB).ite_mem_FP
    (mem_FP_comp (leadingPacket_FP P a) (IntegralMixedOldBankCofactorBits.writer_FP P a R hr))
    (mem_FP_comp (heightPacket_FP P a) (IntegralMixedHeightTableQueryBits.writer_FP P a))

theorem task_leading (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing)
    (q : List Bool) (i : ℕ) (hi : i < birth P q) :
    task P R (pair q (BinaryNatCode.encode i)) = IntegralMixedOldBankCofactorBits.writer P R
      (IntegralMixedOldBankCofactorBits.packet P (bankFamily P D) q i) := by
  simp only [task, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_eq_left hi, leadingPacket]
  rw [IntegralMixedOldBankCofactorBits.packet, IntegralMixedOldBankCofactorBits.count_eq P (bankFamily P D)
    (IntegralMixedFullHistoryFamilyBits.geometry P D)]
  rfl

theorem task_height (P : Parameters) (R : Routing) (q : List Bool) (i : ℕ) (hi : birth P q ≤ i) :
    task P R (pair q (BinaryNatCode.encode i)) = IntegralMixedHeightTableQueryBits.writer P
      (pair q (BinaryNatCode.encode (i - birth P q))) := by
  simp only [task, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    ite_eq_right (not_lt.mpr hi), heightPacket]

noncomputable def entryWord (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (i : ℕ) :=
  if hi : i < birth P q then
    residueBits (((bankFamily P D).state (IntegralMixedVirtualTaskBits.saved P q)).bank.denominator
      ⟨i, hi.trans_eq (IntegralMixedOldHeightBits.bank_birth P D q).symm⟩ : ZMod (modulus P q))
  else IntegralMixedOldHeightBits.value P D (IntegralMixedHeightTableQueryBits.writer P
    (pair q (BinaryNatCode.encode (i - birth P q))))
noncomputable def entry (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (i : ℕ) :=
  Nat.fromBitsLE (entryWord P D q i)

theorem entry_normalized (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) (i : ℕ) :
    BinaryNatCode.encode (entry P D q i) = entryWord P D q i := by
  unfold entry entryWord
  split_ifs
  · simp only [residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · obtain ⟨z, hz⟩ := IntegralMixedOldHeightBits.value_canonical P D
      (IntegralMixedHeightTableQueryBits.writer P (pair q (BinaryNatCode.encode (i - birth P q))))
    rw [← hz]
    simp only [residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

structure RepliesAt (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) : Prop where
  leading : IntegralMixedOldBankCofactorBits.RepliesAt P (bankFamily P D) R reply q
  height : ∀ i < birth P q,
    reply (IntegralMixedHeightTableQueryBits.writer P (pair q (BinaryNatCode.encode i))) =
      IntegralMixedOldHeightBits.value P D (IntegralMixedHeightTableQueryBits.writer P (pair q (BinaryNatCode.encode i)))

theorem task_reply (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (he : RepliesAt P D R reply q) (i : ℕ) (hi : i < count P q) :
    reply (task P R (pair q (BinaryNatCode.encode i))) = BinaryNatCode.encode (entry P D q i) := by
  rw [entry_normalized]
  by_cases HB : i < birth P q
  · rw [task_leading P D R q i HB, entryWord, dite_eq_left HB]
    exact he.leading ⟨i, HB.trans_eq (IntegralMixedOldHeightBits.bank_birth P D q).symm⟩
  · rw [task_height P R q i (not_lt.mp HB), entryWord, dite_eq_right HB]
    exact he.height _ (by unfold count at hi; omega)

noncomputable def program (P : Parameters) (R : Routing) := FixedWidthVectorPass.program (count P) (width P) (task P R)
noncomputable def value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :=
  FixedWidthNatVector.encode (count P q) (width P q) (entry P D q)

theorem certificates (P : Parameters) (a : Access P) (R : Routing) (hr : RoutingAccess R) :
    (program P R).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  FixedWidthVectorPass.certificates _ _ (count_unary P a) (width_unary P a) _ (task_FP P a R hr)

theorem value_at (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (he : RepliesAt P D R reply q) :
    (program P R).value reply q = value P D q :=
  FixedWidthVectorPass.value_at _ _ _ _ _ _ (task_reply P D R reply q he)

theorem requests_frame (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing)
    (reply : List Bool → List Bool) (q c : List Bool) (budget : List Bool → ℕ)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 0) (hp : phase q = 4)
    (hc : (program P R).controller.Requests reply budget q c) : IntegralMixedRoutineTaskBits.Frame P q c := by
  obtain ⟨i, hi, rfl⟩ := FixedWidthVectorPass.requests_coordinate_any (count P) (width P) (task P R) reply budget q c hc
  by_cases HB : i < birth P q
  · rw [task_leading P D R q i HB]
    exact IntegralMixedOldBankCofactorBits.writer_packet_frame P (bankFamily P D) (IntegralMixedFullHistoryFamilyBits.geometry P D)
      R q i (HB.trans_eq (IntegralMixedOldHeightBits.bank_birth P D q).symm)
  · rw [task_height P R q i (not_lt.mp HB)]
    exact IntegralMixedHeightTableQueryBits.writer_frame P q _ hr hp

end LeanCanny.Algebra.IntegralMixedHeightTablePassBits
