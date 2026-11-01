/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.SumSquaresFP
public import LeanCanny.ETR.TermView
/-! # Native indexed access to a term forest, with literal zero padding -/
@[expose] public section
namespace LeanCanny.Encoding.TermForestIndex
open Brackets LeanCanny.ETR

def tail (q : List Bool) : List Bool := afterNode^[(pairSnd q).length] (pairFst q)
def word (q : List Bool) : List Bool := firstNode (tail q)
noncomputable def term (q : List Bool) : Term := TermView.term (word q)

attribute [local irreducible] pair pairFst pairSnd firstNode afterNode

theorem tail_FP : tail ∈ FP := by
  exact iterate_mem_FP_of_step_le afterNode_mem_FP pairFst_mem_FP pairSnd_mem_FP 0
    (fun q n _ => by
      rw [Function.iterate_succ_apply']
      simp only [afterNode,List.length_drop,Nat.add_zero]
      exact Nat.sub_le _ _)

theorem word_FP : word ∈ FP := mem_FP_comp tail_FP firstNode_mem_FP

theorem term_FP : (fun q => (term q).toData.toBits) ∈ FP :=
  mem_FP_of_eq (mem_FP_comp word_FP TermView.normalize_mem_FP) (fun q => TermView.normalize_eq_term (word q))

theorem term_empty : TermView.term []=.const 0 := by
  have H : Grammar.recognizeTerm []=false := by decide
  simp only [TermView.term,H,Bool.false_eq_true,dite_false]

theorem after_empty : afterNode []=[] := by simp only [afterNode,List.drop_nil]
theorem first_empty : firstNode []=[] := by simp only [firstNode,List.take_nil]

theorem term_forest (ts : List Term) (i : ℕ) :
    TermView.term (firstNode (afterNode^[i] (SumSquares.forest ts)))=(ts[i]?).getD (.const 0) := by
  induction i generalizing ts with
  | zero =>
    cases ts with
    | nil => simpa only [Function.iterate_zero_apply,SumSquares.forest_nil,first_empty,List.getElem?_nil,Option.getD_none] using term_empty
    | cons t ts => simp only [Function.iterate_zero_apply,SumSquares.forest_cons,firstNode_toBits_append,
        TermView.term_toBits,List.getElem?_cons_zero,Option.getD_some]
  | succ i IH =>
    cases ts with
    | nil =>
      rw [Function.iterate_succ_apply,SumSquares.forest_nil,after_empty]
      simpa only [SumSquares.forest_nil,List.getElem?_nil,Option.getD_none] using IH []
    | cons t ts =>
      rw [Function.iterate_succ_apply,SumSquares.forest_cons,afterNode_toBits_append]
      simpa only [List.getElem?_cons_succ] using IH ts

theorem term_pair (ts : List Term) (i : ℕ) :
    term (pair (SumSquares.forest ts) (List.replicate i true))=(ts[i]?).getD (.const 0) := by
  simp only [term,word,tail,pairFst_pair,pairSnd_pair,List.length_replicate]
  exact term_forest ts i

end LeanCanny.Encoding.TermForestIndex
