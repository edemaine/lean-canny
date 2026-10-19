/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedProductControllerCorrect
public import LeanCanny.Computation.SubroutineFunction

/-!
# Suspending the product controller for leaf computations

A leaf evaluator receives `pair context (pair factorIndex bitIndex)`. The
parent retains its binary stack while the child runs. Contracting each child
call gives exactly the verified ordinary controller, with the child's actual
output bit; a whole factor or product is never stored in the parent.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedProduct.Suspended
open Complexity
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

def resume {f : List Bool → List Bool} (E : SpaceFunction f) (z : List Bool) : List Bool :=
  pair (pairFst (pairFst z)) (retBits (E.output (pairSnd z)) (evalStack (pairFst z)))

def program {f : List Bool → List Bool} (E : SpaceFunction f) : SubroutineIteration.Program where
  ordinary := Controller.step (fun _ => [])
  request := request
  start := E.init ∘ leafQuery
  advance := E.advance
  halt := E.halt
  resume := resume E

def childTime {f : List Bool → List Bool} (E : SpaceFunction f) (p : List Bool) : ℕ := E.time (leafQuery p)

theorem request_mem_FP : (fun p => [request p]) ∈ FP :=
  ((FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0)).not.and
    ((FPPred.getBit pairSnd_mem_FP (UnaryFn.const 1)).not.and
      (stringEq_fppred (mem_FP_comp query_mem_FP QueryBits.height_mem_FP) (constFn_mem_FP [])))).flag_mem_FP

theorem halted_mem_FP : (fun p => [halted p]) ∈ FP :=
  ((FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0)).and
    (FPPred.getBit pairSnd_mem_FP (UnaryFn.const 1))).flag_mem_FP

theorem output_mem_FP : output ∈ FP :=
  (FPPred.getBit pairSnd_mem_FP (UnaryFn.const 2)).ite_mem_FP (constFn_mem_FP [true]) (constFn_mem_FP [])

theorem resume_mem_FP {f : List Bool → List Bool} (E : SpaceFunction f) : resume E ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hs := mem_FP_comp pairFst_mem_FP evalStack_mem_FP
  have hx := mem_FP_comp pairSnd_mem_FP E.outputFP
  have h := mem_FP_pair hc (retBits_mem_FP hx hs)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem program_polyTime {f : List Bool → List Bool} (E : SpaceFunction f) : (program E).PolyTime := by
  have hs := mem_FP_comp leafQuery_mem_FP E.initFP
  exact ⟨Controller.step_mem_FP (constFn_mem_FP []), request_mem_FP,
    hs, E.advanceFP, E.haltFP, resume_mem_FP E⟩

theorem child_terminates {f : List Bool → List Bool} (E : SpaceFunction f) (p : List Bool) :
    SubroutineIteration.TerminatesAt (program E) p (childTime E p) :=
  ⟨E.before (leafQuery p), E.after (leafQuery p)⟩

theorem step_eq_of_not_request (f g : List Bool → List Bool) (p : List Bool) (hr : request p = false) :
    Controller.step f p = Controller.step g p := by
  simp only [request, decide_eq_false_iff_not] at hr
  simp only [Controller.step, nextState, evalNext]
  split_ifs <;> simp_all

theorem abstractStep_eq_step {f : List Bool → List Bool} (E : SpaceFunction f) (p : List Bool) :
    SubroutineIteration.abstractStep (program E) (childTime E) p = Controller.step f p := by
  by_cases hr : request p = true
  · have hreq := of_decide_eq_true hr
    rcases hreq with ⟨h0, h1, hh⟩
    simp only [SubroutineIteration.abstractStep, program, hr, ↓reduceIte, childTime, Function.comp_apply,
      resume, pairFst_pair, pairSnd_pair, E.correct, Controller.step, nextState, h0, h1, evalNext, hh,
      Bool.false_eq_true]
  · have hf : request p = false := Bool.eq_false_iff.mpr hr
    simp only [SubroutineIteration.abstractStep, program, hf, Bool.false_eq_true, ↓reduceIte]
    exact step_eq_of_not_request _ _ p hf

theorem abstractStep_packet {f : List Bool → List Bool} (E : SpaceFunction f) (c : List Bool) (a : ℕ → ℕ)
    (hl : ∀ i k, (f (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false =
      (a i).testBit k) (s : State) :
    SubroutineIteration.abstractStep (program E) (childTime E) (pair c (stateBits s)) =
      pair c (stateBits (BalancedProduct.step a s)) := by
  rw [abstractStep_eq_step, Controller.step_packet f c a hl]

theorem iterate_packet {f : List Bool → List Bool} (E : SpaceFunction f) (c : List Bool) (a : ℕ → ℕ)
    (hl : ∀ i k, (f (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false =
      (a i).testBit k) (t : ℕ) (s : State) :
    (SubroutineIteration.abstractStep (program E) (childTime E))^[t] (pair c (stateBits s)) =
      pair c (stateBits ((BalancedProduct.step a)^[t] s)) := by
  have he : SubroutineIteration.abstractStep (program E) (childTime E) = Controller.step f :=
    funext (abstractStep_eq_step E)
  rw [he, Controller.iterate_packet f c a hl]

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

end LeanCanny.Algebra.BalancedProduct.Suspended
