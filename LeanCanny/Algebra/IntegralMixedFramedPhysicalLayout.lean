/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalScalar
public import LeanCanny.Algebra.IntegralMixedFramedHeaders
public import LeanCanny.Algebra.IntegralMixedFramedHistorySuccessor
public import LeanCanny.Computation.PolyTimeRange
/-! # Original header tables determine full physical prefix arities

Each original critical tag contributes its physical block and scalar;
other tags contribute one scalar. The count is native unary and preserves
all original-root data, including default births after the stored script.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
open LeanCanny LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedHistoryScript (Instruction chronological paddedPast)
open IntegralMixedHeaderTablesBits (Tables)
open IntegralMixedCommandHeaderBits (lookup command)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def span (P : Parameters) (T : Tables) (q : List Bool) :=
  if (lookup (T.commands (pairFst (pairFst q))) (pairSnd q).length).context=1 then
    block (P.ambient (pairFst (pairFst q)))+1 else 1

theorem span_unary (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    UnaryFn (span P T) := by
  have HR:=IntegralMixedCommandHeaderBits.lookup_readers
    (fun q=>T.commands (pairFst (pairFst q))) (fun q=>(pairSnd q).length)
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) h.commands) (BinaryFn.ofUnary UnaryFn.index)
  have HN:UnaryFn (fun q=>P.ambient (pairFst (pairFst q))) := a.ambient.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  exact UnaryFn.ite (HR.context.eq (BinaryFn.const 1)) (((HN.add (UnaryFn.const 1)).add (HN.add (UnaryFn.const 2))).add (UnaryFn.const 1)) (UnaryFn.const 1)

def prefixArity (P : Parameters) (T : Tables) (q : List Bool) :=
  ∑ j∈Finset.range (pairSnd q).length,span P T (pair (pairFst q) (List.replicate j true))

theorem prefixArity_unary (P : Parameters) (a : Access P) (T : Tables) (h : IntegralMixedHeaderTablesBits.Access T) :
    UnaryFn (prefixArity P T) := by
  have HS:UnaryFn (fun z=>span P T (pair (pairFst (pairFst z)) (pairSnd z))) :=
    (span_unary P a T h).comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
  exact (UnaryFn.sum UnaryFn.index HS).of_eq (fun q=>by simp only [prefixArity,pairFst_pair,pairSnd_pair])

private theorem added_header {n B : ℕ} {P : IntegralMixedHistory.SpatialSource n}
    (c : IntegralMixedFullHistoryScript.Command P B) :
    added c=(if (command c).context=1 then block n+1 else 1) := by
  cases c with
  | integer=>rfl
  | critical=>rfl
  | cut r k=>cases k <;> rfl

theorem padded_arity {n B : ℕ} (fallback : Instruction n B) (cs : List (Instruction n B)) (b : ℕ) :
    arity (paddedPast fallback cs b)=
      ∑ j∈Finset.range b,added ((chronological cs j).getD fallback).command := by
  induction b with
  | zero=>simp only [paddedPast,Finset.range_zero,Finset.sum_empty,Nat.zero_sub,List.replicate_zero,
      IntegralMixedFramedHistoryScript.past,List.take_zero,List.reverse_nil,List.nil_append,arity]
  | succ b ih=>rw [IntegralMixedFramedHistoryScript.paddedPast_succ,arity,ih,Finset.sum_range_succ]

theorem prefixArity_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) (key : List Bool) (b : ℕ) :
    prefixArity P T (pair key (List.replicate b true))=
      arity (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key)) (D.rules (pairFst key)) b) := by
  rw [padded_arity]
  simp only [prefixArity,pairFst_pair,pairSnd_pair,List.length_replicate]
  apply Finset.sum_congr rfl
  intro j _
  simp only [span,pairFst_pair,pairSnd_pair,List.length_replicate,hr.commands]
  rw [IntegralMixedFramedHeaderBits.lookup_words (D.rules (pairFst key))
    (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D (pairFst key)) (by rfl) j,added_header]

theorem slotNumber_drop {n B : ℕ} (cs : List (Instruction n B)) (i : ℕ) (hi : i<cs.length) :
    slotNumber cs i=arity (cs.drop i)-1 := by
  induction cs generalizing i with
  | nil=>simp only [List.length_nil] at hi; omega
  | cons c cs ih=>
    cases i with
    | zero=>rfl
    | succ i=>
      simp only [slotNumber,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,List.drop_succ_cons]
      exact ih i (by simp only [List.length_cons] at hi; omega)
end LeanCanny.Algebra.IntegralMixedFramedPhysicalIndex
