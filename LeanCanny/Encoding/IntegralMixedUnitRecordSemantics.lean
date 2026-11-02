/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedUnitRecordCode
/-! # Decoded unit bodies equal their literal causal row expressions -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedUnitRecordSemantics
open LeanCanny.Algebra IntegralMixedHistory
open IntegralMixedUnitRecordCode
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem get_nil (i : ℕ) : WordList.get [] i = [] := by
  simpa only [WordList.encode, List.getElem?_nil, Option.getD_none] using WordList.get_encode [] i

theorem field_height (n birth : ℕ) (code key : List Bool) :
    IntegralMixedFramedUnitBodyBits.field (fun _ => body n birth code) 0 key = BinaryNatCode.encode (height n code) := by
  simp only [IntegralMixedFramedUnitBodyBits.field, body, WordList.get_encode, List.getElem?_cons_zero, Option.getD_some]

theorem field_physical (n birth : ℕ) (code key : List Bool) :
    IntegralMixedFramedUnitBodyBits.field (fun _ => body n birth code) 1 key = physicalRows n birth code := by
  simp only [IntegralMixedFramedUnitBodyBits.field, body, WordList.get_encode, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]

theorem field_virtual (n birth : ℕ) (code key : List Bool) :
    IntegralMixedFramedUnitBodyBits.field (fun _ => body n birth code) 2 key = virtualRows n birth code := by
  simp only [IntegralMixedFramedUnitBodyBits.field, body, WordList.get_encode, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]

theorem expression_row (code : List Bool) (birth i : ℕ) :
    (if (pairFst (IntegralMixedUnitRowCode.row code birth i))[0]?.getD false then
      AffineExpr.reference (Nat.fromBitsLE (pairSnd (IntegralMixedUnitRowCode.row code birth i))) else .constant 0) =
      IntegralMixedUnitRowCode.expression code birth i := by
  simp only [IntegralMixedUnitRowCode.row, pairFst_pair, pairSnd_pair, List.getElem?_cons_zero, Option.getD_some,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, IntegralMixedUnitRowCode.expression, decide_eq_true_eq]

theorem physical_expression (n birth : ℕ) (code key : List Bool) (i : ℕ) (hi : i<n+1) :
    IntegralMixedFramedUnitBodyBits.expression (fun _ => body n birth code) true key i =
      if critical code then IntegralMixedUnitRowCode.expression (field code 6) birth i else .constant 0 := by
  unfold IntegralMixedFramedUnitBodyBits.expression IntegralMixedFramedUnitBodyBits.active IntegralMixedFramedUnitBodyBits.reference
    IntegralMixedFramedUnitBodyBits.rowWord
  rw [ite_eq_left (rfl : (true : Bool) = true), field_physical]
  unfold physicalRows
  by_cases hc : critical code = true
  · rw [ite_eq_left hc, ite_eq_left hc, IntegralMixedUnitRowCode.table_packet, IntegralMixedUnitRowCode.get_table _ _ _ _ hi]
    exact expression_row _ _ _
  · rw [ite_eq_right hc, ite_eq_right hc, get_nil]
    change (if (false : Bool) then AffineExpr.constant 0 else AffineExpr.constant 0) = .constant 0
    simp only [Bool.false_eq_true, ite_false]

theorem virtual_expression (n birth : ℕ) (code key : List Bool) (i : ℕ) (hi : i<n+1) :
    IntegralMixedFramedUnitBodyBits.expression (fun _ => body n birth code) false key i =
      IntegralMixedUnitRowCode.expression (field code 7) birth i := by
  unfold IntegralMixedFramedUnitBodyBits.expression IntegralMixedFramedUnitBodyBits.active IntegralMixedFramedUnitBodyBits.reference
    IntegralMixedFramedUnitBodyBits.rowWord
  rw [ite_eq_right (by decide : (false : Bool) ≠ true), field_virtual]
  unfold virtualRows
  rw [IntegralMixedUnitRowCode.table_packet, IntegralMixedUnitRowCode.get_table _ _ _ _ hi]
  exact expression_row _ _ _

theorem formal_row_zero (n birth : ℕ) (code key : List Bool) :
    IntegralMixedFramedUnitBodyBits.expression (fun _ => body n birth code) false key (n+1) = .constant 0 := by
  unfold IntegralMixedFramedUnitBodyBits.expression IntegralMixedFramedUnitBodyBits.active IntegralMixedFramedUnitBodyBits.reference
    IntegralMixedFramedUnitBodyBits.rowWord
  rw [ite_eq_right (by decide : (false : Bool) ≠ true), field_virtual]
  unfold virtualRows
  rw [IntegralMixedUnitRowCode.table_packet, IntegralMixedUnitRowCode.get_table_outside _ _ _ _ le_rfl]
  change (if (false : Bool) then AffineExpr.constant 0 else AffineExpr.constant 0) = .constant 0
  simp only [Bool.false_eq_true, ite_false]

theorem decoded_height (n birth : ℕ) (code key : List Bool) :
    Nat.fromBitsLE (IntegralMixedFramedUnitBodyBits.field (fun _ => body n birth code) 0 key) = height n code := by
  rw [field_height, BinaryNatCode.encode, Nat.fromBitsLE_bits]
end LeanCanny.Encoding.IntegralMixedUnitRecordSemantics
