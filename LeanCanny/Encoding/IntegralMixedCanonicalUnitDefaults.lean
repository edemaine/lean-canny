/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalCanonicalUnitSnapshot
/-! # Stable producer labels, causal rows, and total empty-record semantics -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCanonicalUnitDefaults
open LeanCanny.Algebra IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem get_nil (i : ℕ) : WordList.get [] i=[] := by
  simpa only [WordList.encode, List.getElem?_nil, Option.getD_none] using WordList.get_encode [] i

/-- An original birth label is converted to the newest-first retained index. -/
theorem expression_producer (code : List Bool) (birth i : ℕ)
    (ha : IntegralMixedUnitRowCode.active code birth i) :
    IntegralMixedUnitRowCode.expression code birth i =
      .reference (birth-1-IntegralMixedUnitRowCode.producer code i) :=
  ite_eq_left ha

/-- Forward references and absent flag bits denote literal zero. -/
theorem expression_unavailable (code : List Bool) (birth i : ℕ)
    (hb : birth ≤ IntegralMixedUnitRowCode.producer code i) :
    IntegralMixedUnitRowCode.expression code birth i = .constant 0 := by
  unfold IntegralMixedUnitRowCode.expression
  apply ite_eq_right
  intro ha
  exact Nat.not_lt_of_ge hb (IntegralMixedUnitRowCode.producer_bound _ _ _ ha)

theorem expression_nil (birth i : ℕ) : IntegralMixedUnitRowCode.expression [] birth i = .constant 0 := by
  unfold IntegralMixedUnitRowCode.expression IntegralMixedUnitRowCode.active
  rw [get_nil]
  simp only [show (pairFst ([] : List Bool))[0]?.getD false = false from rfl, Bool.false_eq_true, false_and, ite_false]

theorem physical_nil (n birth : ℕ) (i : Fin (n+1)) :
    (IntegralMixedCanonicalUnitRuleBits.physical n birth []).heights i = .constant 0 := by
  change IntegralMixedUnitRowCode.expression (IntegralMixedUnitRecordCode.field [] 6) birth i.val = _
  rw [IntegralMixedUnitRecordCode.field, get_nil, expression_nil]

theorem virtual_nil (n : ℕ) (hn : 0<n) (birth : ℕ) (i : Fin (n+1)) :
    ((IntegralMixedCanonicalUnitRuleBits.virtual n hn birth []).critical).heights i = .constant 0 := by
  change IntegralMixedUnitRowCode.expression (IntegralMixedUnitRecordCode.field [] 7) birth i.val = _
  rw [IntegralMixedUnitRecordCode.field, get_nil, expression_nil]

theorem virtual_nil_height (n : ℕ) (hn : 0<n) (birth : ℕ) :
    (IntegralMixedCanonicalUnitRuleBits.virtual n hn birth []).height.val = 0 := by
  change IntegralMixedUnitRecordCode.height n [] = 0
  unfold IntegralMixedUnitRecordCode.height IntegralMixedUnitRecordCode.field
  rw [get_nil]
  exact Nat.zero_mod _

/-- The formal nilpotent coordinate has no physical-row selector. -/
theorem formal_row (n birth : ℕ) (code key : List Bool) :
    IntegralMixedFramedUnitBodyBits.expression (fun _ => IntegralMixedUnitRecordCode.body n birth code)
      false key (n+1) = .constant 0 :=
  IntegralMixedUnitRecordSemantics.formal_row_zero n birth code key
end LeanCanny.Encoding.IntegralMixedCanonicalUnitDefaults
