/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateTasks
public import LeanCanny.Algebra.IntegralMixedHeightTablePass
public import LeanCanny.Algebra.PoweredPrefixProduct

/-! # A limit coefficient streams older producer leadings before its critical entry

Only earlier births supply the bank denominator. The last request is to the
lower critical routine at the original birth. No additional scalar phase or
supplied denominator evaluator is needed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitCoordinateRequests
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedLimitCoordinateTasks.critical
  IntegralMixedOldBankCofactorBits.writer IntegralMixedHeightTablePassBits.leadingPacket

noncomputable def task (P : Parameters) (F : Family) (R : Routing) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd p) < birth P (pairFst p) then
    IntegralMixedOldBankCofactorBits.writer P R (IntegralMixedHeightTablePassBits.leadingPacket P p)
  else IntegralMixedLimitCoordinateTasks.critical P F (pairFst p)

theorem task_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (R : Routing) (hr : RoutingAccess R) : task P F R ∈ FP := by
  unfold task
  exact ((BinaryFn.fromBits pairSnd_mem_FP).lt
    ((BinaryFn.ofUnary (IntegralMixedOldHeightBits.birth_unary P a)).comp pairFst_mem_FP)).ite_mem_FP
    (mem_FP_comp (IntegralMixedHeightTablePassBits.leadingPacket_FP P a)
      (IntegralMixedOldBankCofactorBits.writer_FP P a R hr))
    (mem_FP_comp pairFst_mem_FP (IntegralMixedLimitCoordinateTasks.critical_FP P a F h))

theorem task_leading (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (R : Routing) (q : List Bool) (i : ℕ) (hi : i < birth P q) :
    task P F R (pair q (BinaryNatCode.encode i)) =
      IntegralMixedOldBankCofactorBits.writer P R (IntegralMixedOldBankCofactorBits.packet P F q i) := by
  simp only [task, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_eq_left hi]
  congr 1
  simp only [IntegralMixedHeightTablePassBits.leadingPacket, IntegralMixedOldBankCofactorBits.packet,
    IntegralMixedOldBankCofactorBits.count_eq P F g q, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem task_last (P : Parameters) (F : Family) (R : Routing) (q : List Bool) :
    task P F R (pair q (BinaryNatCode.encode (birth P q))) = IntegralMixedLimitCoordinateTasks.critical P F q := by
  simp only [task, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Nat.lt_irrefl, ite_false]

theorem task_frame (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (R : Routing) (q : List Bool) (hq : IntegralMixedRoutineTaskBits.routine P q = 4)
    (i : ℕ) (hi : i < birth P q + 1) :
    IntegralMixedRoutineTaskBits.Frame P q (task P F R (pair q (BinaryNatCode.encode i))) := by
  by_cases H : i < birth P q
  · rw [task_leading P F g R q i H]
    exact IntegralMixedOldBankCofactorBits.writer_packet_frame P F g R q i
      (H.trans_eq (IntegralMixedOldBankCofactorBits.count_eq P F g q).symm)
  · have HI : i = birth P q := by omega
    rw [HI, task_last]
    exact IntegralMixedLimitCoordinateTasks.critical_frame P F q hq

noncomputable def exponent (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  IntegralMixedCoordinateCoefficientTasks.choiceBound P F q - 1 - get P .coefficient q

theorem exponent_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    BinaryFn (exponent P F) :=
  ((IntegralMixedCoordinateCoefficientTasks.choiceBound_binary P a F h).sub (BinaryFn.const 1)).sub
    (get_binary P a .coefficient)

def modulusPredecessor (P : Parameters) (q : List Bool) : ℕ := modulus P q - 1

theorem modulusPredecessor_binary (P : Parameters) (a : Access P) : BinaryFn (modulusPredecessor P) :=
  (modulus_binary P a).sub (BinaryFn.const 1)

theorem modulusPredecessor_value (P : Parameters) (q : List Bool) : modulusPredecessor P q + 1 = modulus P q := by
  unfold modulusPredecessor
  have H := modulus_ne_zero P q
  omega

noncomputable def program (P : Parameters) (F : Family) (R : Routing) : RecursiveFold.Program :=
  PoweredPrefixProduct.program (birth P) (exponent P F) (modulusPredecessor P) (task P F R)

theorem certificates (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (R : Routing) (hr : RoutingAccess R) :
    (program P F R).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  PoweredPrefixProduct.certificates _ _ _ _ (BinaryFn.ofUnary (IntegralMixedOldHeightBits.birth_unary P a))
    (exponent_binary P a F h) (modulusPredecessor_binary P a) (task_FP P a F h R hr)

end LeanCanny.Algebra.IntegralMixedLimitCoordinateRequests
