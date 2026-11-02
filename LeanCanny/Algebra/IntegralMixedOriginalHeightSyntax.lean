/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOriginalScalarCells
/-! # Affine and slope cells are read from original rule syntax -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOriginalRuleBodyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def heightSource (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (q : List Bool) :=
  if get P .slot8 q < arity P q then
    WordList.get (if get P .slot15 q = 1 then field h.writer 1 (IntegralMixedVirtualTaskBits.saved P q)
      else field h.writer 3 (IntegralMixedVirtualTaskBits.saved P q)) (get P .slot8 q)
  else IntegralMixedAffineCode.encode (.constant 0)

theorem heightSource_FP (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) :
    heightSource P D h ∈ FP := by
  have HQ := IntegralMixedVirtualTaskBits.saved_FP P a
  have HB := ((get_binary P a .slot15).eq (BinaryFn.const 1)).ite_mem_FP
    (mem_FP_comp (f := IntegralMixedVirtualTaskBits.saved P) (g := field h.writer 1) HQ (field_FP _ h.writer_FP 1)) (mem_FP_comp (f := IntegralMixedVirtualTaskBits.saved P) (g := field h.writer 3) HQ (field_FP _ h.writer_FP 3))
  exact ((get_binary P a .slot8).lt (BinaryFn.ofUnary (arity_unary P a))).ite_mem_FP
    (IntegralMixedCommandHeaderBits.fetched_FP _ _ HB (get_binary P a .slot8)) (constFn_mem_FP _)

theorem heightSource_eq (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (q : List Bool) :
    heightSource P D h q = IntegralMixedAffineCode.encode (IntegralMixedHeightCellsBits.affine P D q) := by
  unfold heightSource IntegralMixedHeightCellsBits.affine arity
  dsimp only
  by_cases hi : get P .slot8 q < P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1
  · rw [ite_eq_left hi, dite_eq_left hi]
    by_cases hx : get P .slot15 q = 1
    · rw [ite_eq_left hx, physical_heights, get_ofFn _ _ hi, IntegralMixedHeightCellsBits.rule_physical P D q hx]
      rfl
    · rw [ite_eq_right hx, virtual_heights, get_ofFn _ _ hi, IntegralMixedHeightCellsBits.rule_virtual P D q hx]
      rfl
  · rw [ite_eq_right hi, dite_eq_right hi]

def slopeCode (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (q : List Bool) :=
  if get P .slot8 q = Nat.fromBitsLE (field h.writer 5 (IntegralMixedVirtualTaskBits.saved P q)) then
    field h.writer 6 (IntegralMixedVirtualTaskBits.saved P q) else SignStatisticBits.integerCode 0

theorem slopeCode_FP (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) :
    slopeCode P D h ∈ FP := by
  have HQ := IntegralMixedVirtualTaskBits.saved_FP P a
  exact ((get_binary P a .slot8).eq (BinaryFn.fromBits (mem_FP_comp (f := IntegralMixedVirtualTaskBits.saved P) (g := field h.writer 5) HQ (field_FP _ h.writer_FP 5)))).ite_mem_FP
    (mem_FP_comp (f := IntegralMixedVirtualTaskBits.saved P) (g := field h.writer 6) HQ (field_FP _ h.writer_FP 6)) (constFn_mem_FP _)

theorem slopeCode_eq (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Access P D) (q : List Bool) :
    slopeCode P D h q = SignStatisticBits.integerCode
      (if get P .slot8 q = (virtualRule P D (IntegralMixedVirtualTaskBits.saved P q)).height.val then
        (virtualRule P D (IntegralMixedVirtualTaskBits.saved P q)).slope else 0) := by
  rw [slopeCode, height_field, slope_field, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs <;> rfl
end LeanCanny.Algebra.IntegralMixedOriginalRuleBodyBits
