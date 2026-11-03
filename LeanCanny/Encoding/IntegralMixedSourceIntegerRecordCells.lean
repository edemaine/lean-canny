/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordSource
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQIndexedOriginal
/-! # Native affine and scale cells across the actual integer-prelude boundary -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def rowValue (P : Parameters) (N : List Bool→ℕ) (physical : Bool) (key : List Bool) (i : ℕ) : AffineExpr :=
  if IntegralMixedUnitRecordCode.critical (selectedCode P N key)=physical then
    IntegralMixedCausalUnitRecordBits.row (selectedCode P N key) physical (prefixLength P key) i else .constant 0
noncomputable def mask (P : Parameters) (N : List Bool→ℕ) (physical : Bool) (key : List Bool) :=
  if IntegralMixedUnitRecordCode.critical (selectedCode P N key)=physical then
    IntegralMixedUnitRecordCode.field (selectedCode P N key) (if physical then 12 else 13) else []

theorem mask_FP (P : Parameters) (a : Access P) (N : List Bool→ℕ) (hN : UnaryFn N) (physical : Bool) : mask P N physical∈FP := by
  have HC := selectedCode_FP P N a hN
  have HF := FPPred.getBit (mem_FP_comp (f:=selectedCode P N) (g:=fun w => WordList.get w 0) HC (IntegralMixedCommandHeaderBits.get_FP 0)) (UnaryFn.const 0)
  have HP : FPPred (fun key => IntegralMixedUnitRecordCode.critical (selectedCode P N key)=physical) := by
    cases physical
    · exact HF.not.of_iff (fun _ => by simp only [Function.comp_apply,IntegralMixedUnitRecordCode.critical,IntegralMixedUnitRecordCode.field,Bool.not_eq_true])
    · exact HF
  exact mem_FP_of_eq (HP.ite_mem_FP (mem_FP_comp (f:=selectedCode P N) (g:=fun w => WordList.get w _) HC
    (IntegralMixedCommandHeaderBits.get_FP _)) (constFn_mem_FP [])) (fun _ => rfl)

noncomputable def rowSyntax (P : Parameters) (N : List Bool→ℕ) (physical : Bool) (z : List Bool) :=
  IntegralMixedAffineCode.encode (rowValue P N physical (pairFst z) (Nat.fromBitsLE (pairSnd z)))

theorem rowSyntax_FP (P : Parameters) (a : Access P) (N : List Bool→ℕ) (hN : UnaryFn N) (physical : Bool) : rowSyntax P N physical∈FP := by
  have HC := mem_FP_comp pairFst_mem_FP (selectedCode_FP P N a hN)
  have HF := FPPred.getBit (mem_FP_comp (f:=fun z => selectedCode P N (pairFst z)) (g:=fun w => WordList.get w 0) HC (IntegralMixedCommandHeaderBits.get_FP 0)) (UnaryFn.const 0)
  have HP : FPPred (fun z => IntegralMixedUnitRecordCode.critical (selectedCode P N (pairFst z))=physical) := by
    cases physical
    · exact HF.not.of_iff (fun _ => by simp only [Function.comp_apply,IntegralMixedUnitRecordCode.critical,IntegralMixedUnitRecordCode.field,Bool.not_eq_true])
    · exact HF
  have HE := IntegralMixedCausalUnitBodyBits.row_encode_FP HC
    ((IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp pairFst_mem_FP) (BinaryFn.fromBits pairSnd_mem_FP) physical
  apply mem_FP_of_eq (HP.ite_mem_FP HE (constFn_mem_FP (IntegralMixedAffineCode.encode (.constant 0))))
  intro z
  unfold rowSyntax rowValue
  split_ifs <;> rfl

def rowQuery (P : Parameters) (q : List Bool) :=
  pair (IntegralMixedVirtualTaskBits.saved P q) (BinaryNatCode.encode (get P .slot8 q))

theorem rowQuery_FP (P : Parameters) (a : Access P) : rowQuery P∈FP :=
  mem_FP_pair (IntegralMixedVirtualTaskBits.saved_FP P a) (get_binary P a .slot8).bits_mem_FP

noncomputable def word (P : Parameters) (N : List Bool→ℕ) (q : List Bool) :=
  if get P .slot8 q<IntegralMixedOriginalRuleBodyBits.arity P q then
    rowSyntax P N (decide (get P .slot15 q=1)) (rowQuery P q)
  else IntegralMixedAffineCode.encode (.constant 0)

attribute [local irreducible] rowQuery rowSyntax IntegralCriticalHistoryTask.get

theorem word_FP (P : Parameters) (a : Access P) (N : List Bool→ℕ) (hN : UnaryFn N) : word P N∈FP := by
  have HC := (get_binary P a .slot15).eq (BinaryFn.const 1)
  have HB := (get_binary P a .slot8).lt (BinaryFn.ofUnary (IntegralMixedOriginalRuleBodyBits.arity_unary P a))
  have HT := mem_FP_comp (f:=rowQuery P) (g:=rowSyntax P N true) (rowQuery_FP P a) (rowSyntax_FP P a N hN true)
  have HF := mem_FP_comp (f:=rowQuery P) (g:=rowSyntax P N false) (rowQuery_FP P a) (rowSyntax_FP P a N hN false)
  apply mem_FP_of_eq (HB.ite_mem_FP (HC.ite_mem_FP HT HF)
    (constFn_mem_FP (IntegralMixedAffineCode.encode (.constant 0))))
  intro q
  simp only [word,Function.comp_apply]
  split_ifs with hi hx <;> simp_all only [decide_true,decide_false]

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
