/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalPlanSnapshot
/-! # Native original mode/height metadata supplies the causal slope snapshot

The sole writer encodes original record flags and bounded height labels.
It neither evaluates nor serializes a current denominator.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalPlanBits
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def modeWords (P : Parameters) (R : ∀ root,List (Record (P.ambient root) (P.width root))) (root : List Bool) :=
  WordList.encode ((R root).reverse.map fun r => pair [templateCurrent r.template] (BinaryNatCode.encode (templateHeight r.template)))
noncomputable def modeRead (P : Parameters) (R : ∀ root,List (Record (P.ambient root) (P.width root))) (key : List Bool) :=
  WordList.get (modeWords P R (pairFst key)) (IntegralMixedFramedHistoryFamilyBits.prefixLength P key)

theorem modeRead_FP (P : Parameters) (a : Access P)
    (R : ∀ root,List (Record (P.ambient root) (P.width root))) (h : modeWords P R∈FP) : modeRead P R∈FP := by
  have H := mem_FP_comp (g:=WordList.reader) (mem_FP_pair (mem_FP_comp pairFst_mem_FP h)
    (BinaryFn.ofUnary (IntegralMixedFullHistoryFamilyBits.prefix_unary P a)).bits_mem_FP) WordList.reader_FP
  exact mem_FP_of_eq H (fun key => by simp only [Function.comp_apply,WordList.reader,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,modeRead])

theorem current_modeRead (P : Parameters) (R : ∀ root,List (Record (P.ambient root) (P.width root))) (key : List Bool) :
    (pairFst (modeRead P R key))[0]?.getD false=current P R key := by
  unfold modeRead modeWords current
  rw [WordList.get_encode,List.getElem?_map]
  cases hr : (R (pairFst key)).reverse[IntegralMixedFramedHistoryFamilyBits.prefixLength P key]? with
  | none => rfl
  | some r => rw [Option.map_some,Option.getD_some,pairFst_pair]; rfl

theorem height_modeRead (P : Parameters) (R : ∀ root,List (Record (P.ambient root) (P.width root))) (key : List Bool) :
    Nat.fromBitsLE (pairSnd (modeRead P R key))=height P R key := by
  unfold modeRead modeWords height
  rw [WordList.get_encode,List.getElem?_map]
  cases hr : (R (pairFst key)).reverse[IntegralMixedFramedHistoryFamilyBits.prefixLength P key]? with
  | none => rfl
  | some r => simp only [Option.map_some,Option.getD_some,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem metadata (P : Parameters) (a : Access P)
    (R : ∀ root,List (Record (P.ambient root) (P.width root))) (h : modeWords P R∈FP) : Metadata P R where
  current_FP := by
    have H := (FPPred.getBit (mem_FP_comp (modeRead_FP P a R h) pairFst_mem_FP) (UnaryFn.const 0)).flag_mem_FP
    apply mem_FP_of_eq H
    intro key
    rw [← current_modeRead P R key]
    simp only [Function.comp_apply]
    have HB (b : Bool) : [decide (b=true)]=[b] := by cases b <;> rfl
    exact HB _
  height_binary := (BinaryFn.fromBits (mem_FP_comp (modeRead_FP P a R h) pairSnd_mem_FP)).of_eq (height_modeRead P R)
end LeanCanny.Algebra.IntegralMixedCausalPlanBits
