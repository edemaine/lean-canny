/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedTerminalTarskiHead
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateHeadWidth
/-! # Original cap/width ceilings for the actual eta-shift allowance -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedShiftDegreeCeiling
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def headCeiling (S B : ℕ) :=
  (2^B-1)+UniformIntegralPowerSchedule.birth S (2^B) S*(S*(2^B-1))
def shiftCeiling (S B T : ℕ) := (T+1)*2^(headCeiling S B).size

theorem headCeiling_binary {S B : List Bool → ℕ} (hS : UnaryFn S) (hB : UnaryFn B) :
    BinaryFn (fun c => headCeiling (S c) (B c)) := by
  have HN := (BinaryFn.const 2).powUnary hB
  exact (HN.sub (BinaryFn.const 1)).add
    ((UniformIntegralPowerSchedule.birth_binary hS HN hS).mul
      ((BinaryFn.ofUnary hS).mul (HN.sub (BinaryFn.const 1))))

theorem shiftCeiling_binary {S B T : List Bool → ℕ} (hS : UnaryFn S) (hB : UnaryFn B) (hT : UnaryFn T) :
    BinaryFn (fun c => shiftCeiling (S c) (B c) (T c)) := by
  have HW : UnaryFn (fun c => (headCeiling (S c) (B c)).size) :=
    (UnaryFn.length (headCeiling_binary hS hB).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact (BinaryFn.ofUnary (hT.add (UnaryFn.const 1))).mul ((BinaryFn.const 2).powUnary HW)

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (parent terminal : List Bool → List Bool)

theorem head_degree_bound (q : List Bool) :
    IntegralMixedFramedCoordinatePackedBits.degreeBound P D H parent
      (IntegralMixedSelectedCoordinateHead.fullParameter P parent) q ≤
      headCeiling (P.cap (RankedHistoryTask.root (parent q))+1) (P.width (RankedHistoryTask.root (parent q))) := by
  let S := P.cap (RankedHistoryTask.root (parent q))+1
  let N := 2^P.width (RankedHistoryTask.root (parent q))
  have HM : (IntegralMixedFramedAllCoordinateSourceBits.source P D H).arity (parent q) ≤ S := by
    rw [IntegralMixedFramedAllCoordinateSourceBits.arity]
    exact min_le_right _ _
  have HB := UniformIntegralPowerSchedule.birth_le S N
    ((IntegralMixedFramedAllCoordinateSourceBits.source P D H).arity (parent q)-1) (by omega)
  have HP := Nat.mul_le_mul_right (N-1) HM
  have HD : IntegralMixedFramedAllCoordinateSourceBits.degree P D H (parent q) ≤
      UniformIntegralPowerSchedule.birth S N S*(S*(N-1)) := by
    unfold IntegralMixedFramedAllCoordinateSourceBits.degree
    rw [IntegralMixedFramedAllCoordinateSourceBits.width]
    exact Nat.mul_le_mul HB HP
  exact Nat.add_le_add_left HD _

theorem source_degree_bound (L F C : List Bool → ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (selected : List Bool → ℕ) (q : List Bool) :
    RationalMonomialParameterShift.sourceDegree
      (IntegralMixedFramedTerminalParameterShiftBits.endpointFamily P D H L F C hs terminal selected)
      (IntegralMixedFramedCoordinateBivariateBits.nativeWidth P D H parent
        (IntegralMixedSelectedCoordinateHead.fullParameter P parent)) q ≤
      shiftCeiling (P.cap (RankedHistoryTask.root (parent q))+1) (P.width (RankedHistoryTask.root (parent q)))
        (P.cap (pairFst (terminal q))+1) := by
  have HM : (IntegralMixedFramedWindowQuery.family P D H L F C hs terminal selected).arity q ≤
      P.cap (pairFst (terminal q))+1 := by
    change (IntegralMixedFramedHistoryFamilyBits.family P D H).birth (terminal q) ≤ _
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
    exact min_le_right _ _
  have HW : IntegralMixedFramedCoordinateBivariateBits.nativeWidth P D H parent
      (IntegralMixedSelectedCoordinateHead.fullParameter P parent) q ≤
      (headCeiling (P.cap (RankedHistoryTask.root (parent q))+1) (P.width (RankedHistoryTask.root (parent q)))).size :=
    Nat.size_le_size (head_degree_bound P D H parent q)
  unfold RationalMonomialParameterShift.sourceDegree shiftCeiling
  exact Nat.mul_le_mul (Nat.add_le_add_right HM 1) (Nat.pow_le_pow_right (by decide) HW)

end LeanCanny.Algebra.IntegralMixedFramedShiftDegreeCeiling
