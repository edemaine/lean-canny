/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedProductControllerCorrect
public import LeanCanny.Computation.SpaceIteration

/-! # Space-bounded leaf queries in the balanced-product transition

Native branching composes leaf access with the FP stack updates. The resulting
transition is the mathematical encoded controller, with no child machine state. -/

@[expose] public section

namespace LeanCanny.Algebra.BalancedProduct.SpaceStep

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open Controller

def request (p : List Bool) : Bool := decide
  (¬ (pairSnd p)[0]?.getD false = true ∧ ¬ (pairSnd p)[1]?.getD false = true ∧
    QueryBits.height (query p) = [])

def halted (p : List Bool) : Bool := decide
  ((pairSnd p)[0]?.getD false = true ∧ (pairSnd p)[1]?.getD false = true)

def output (p : List Bool) : List Bool := if (pairSnd p)[2]?.getD false then [true] else []

def resume (z : List Bool) : List Bool :=
  pair (pairFst (pairFst z)) (retBits (pairSnd z) (evalStack (pairFst z)))

theorem request_mem_FP : (fun p => [request p]) ∈ FP :=
  ((FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0)).not.and
    ((FPPred.getBit pairSnd_mem_FP (UnaryFn.const 1)).not.and
      (stringEq_fppred (mem_FP_comp query_mem_FP QueryBits.height_mem_FP) (constFn_mem_FP [])))).flag_mem_FP

theorem halted_mem_FP : (fun p => [halted p]) ∈ FP :=
  ((FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0)).and
    (FPPred.getBit pairSnd_mem_FP (UnaryFn.const 1))).flag_mem_FP

theorem output_mem_FP : output ∈ FP :=
  (FPPred.getBit pairSnd_mem_FP (UnaryFn.const 2)).ite_mem_FP (constFn_mem_FP [true]) (constFn_mem_FP [])

theorem resume_mem_FP : resume ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hs := mem_FP_comp pairFst_mem_FP evalStack_mem_FP
  have hx := pairSnd_mem_FP
  have h := mem_FP_pair hc (retBits_mem_FP hx hs)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem step_eq_of_not_request (f g : List Bool → List Bool) (p : List Bool) (hr : request p = false) :
    Controller.step f p = Controller.step g p := by
  simp only [request, decide_eq_false_iff_not] at hr
  simp only [Controller.step, nextState, evalNext]
  split_ifs <;> simp_all

theorem stepEvaluator {f : List Bool → List Bool} (E : SpaceFunction f) :
    SpaceFunction (Controller.step f) := by
  let R := (E.precompose leafQuery leafQuery_mem_FP).withInput.postcompose resume resume_mem_FP
  let B := SpaceFunction.branch request request_mem_FP R
    (SpaceFunction.ofFP (Controller.step (fun _ => [])) (Controller.step_mem_FP (constFn_mem_FP [])))
  refine B.congr (funext fun p => ?_)
  change (if request p then resume (pair p (f (leafQuery p)))
    else Controller.step (fun _ => []) p) = Controller.step f p
  by_cases hr : request p = true
  · obtain ⟨h0, h1, hh⟩ := of_decide_eq_true hr
    simp only [hr, reduceIte, resume, pairFst_pair, pairSnd_pair,
      Controller.step, nextState, h0, h1, evalNext, hh, Bool.false_eq_true]
  · have hf : request p = false := Bool.eq_false_iff.mpr hr
    simp only [hf, Bool.false_eq_true, reduceIte]
    exact step_eq_of_not_request _ _ p hf

theorem halted_packet (c : List Bool) (s : State) : halted (pair c (stateBits s)) = isDone s := by
  cases s <;> simp [halted, stateBits, isDone]

theorem request_packet (c : List Bool) (s : State) : request (pair c (stateBits s)) =
    match s with | .eval q _ => decide (q.height = 0) | _ => false := by
  cases s <;> simp [request, query, body, stateBits]

theorem leafQuery_packet (c : List Bool) (q : Query) (s : List Frame) :
    leafQuery (pair c (stateBits (.eval q s))) =
      pair c (pair (BinaryNatCode.encode q.node) (BinaryNatCode.encode q.index)) := by
  simp [leafQuery, query, body, stateBits]

theorem output_done (c : List Bool) (b : Bool) : output (pair c (stateBits (.done b))) =
    if b then [true] else [] := by simp [output, stateBits]

end LeanCanny.Algebra.BalancedProduct.SpaceStep
