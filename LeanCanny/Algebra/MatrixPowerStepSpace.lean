/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerControllerCorrect
public import LeanCanny.Computation.SpaceIteration

/-! # Space-bounded entry queries in a matrix-power transition

Exponent-one requests compose the native entry certificate with FP query and
return writers. Other transitions use FP control arithmetic. The composed
transition agrees with the mathematical power controller. -/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower.Controller

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation

def needsEntry (p : List Bool) : Bool :=
  if (pairSnd p)[0]?.getD false = true then false
  else if (pairSnd p)[1]?.getD false = true then false
  else decide (QueryBits.exponent (payload p) = [true])

theorem needsEntry_mem_FP : (fun p => [needsEntry p]) ∈ FP := by
  have he := mem_FP_comp payload_mem_FP QueryBits.exponent_mem_FP
  have hflag := (stringEq_fppred he (constFn_mem_FP [true])).flag_mem_FP
  have hret := (FPPred.getBit pairSnd_mem_FP (UnaryFn.const 1)).ite_mem_FP
    (constFn_mem_FP [false]) hflag
  have h := (FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0)).ite_mem_FP
    (constFn_mem_FP [false]) hret
  exact mem_FP_of_eq h (fun p => by
    simp only [needsEntry, Function.comp_apply]
    split_ifs <;> simp_all)

def entryInput (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (QueryBits.row (payload p)) (QueryBits.col (payload p)))

theorem entryInput_mem_FP : entryInput ∈ FP := by
  have hi := mem_FP_comp payload_mem_FP QueryBits.row_mem_FP
  have hj := mem_FP_comp payload_mem_FP QueryBits.col_mem_FP
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_pair hi hj)
  exact mem_FP_of_eq h (fun _ => rfl)

def resumeEntry (output : List Bool → List Bool) (packet : List Bool) : List Bool :=
  let p := pairFst packet
  pair (pairFst p) (retBits (output (pairSnd packet)) (stack p))

theorem resumeEntry_mem_FP {output : List Bool → List Bool} (ho : output ∈ FP) :
    resumeEntry output ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hv := mem_FP_comp pairSnd_mem_FP ho
  have hs := mem_FP_comp pairFst_mem_FP stack_mem_FP
  have h := mem_FP_pair hc (retBits_mem_FP hv hs)
  exact mem_FP_of_eq h (fun _ => rfl)

def withoutEntry (ops : Callbacks) : Callbacks := { ops with entry := fun _ => [] }

structure Callbacks.ControlsPolyTime (ops : Callbacks) : Prop where
  dimension : ops.dimension ∈ FP
  zero : ops.zero ∈ FP
  one : ops.one ∈ FP
  combine : ops.combine ∈ FP

theorem withoutEntry_polyTime (ops : Callbacks) (hops : ops.ControlsPolyTime) :
    (withoutEntry ops).PolyTime :=
  ⟨hops.dimension, hops.zero, hops.one, constFn_mem_FP [], hops.combine⟩

theorem step_withoutEntry (ops : Callbacks) (p : List Bool) (hr : needsEntry p = false) :
    step (withoutEntry ops) p = step ops p := by
  by_cases hd : (pairSnd p)[0]?.getD false = true
  · simp only [step, nextState, hd, ↓reduceIte]
  by_cases ht : (pairSnd p)[1]?.getD false = true
  · simp only [step, nextState, hd, ht, ↓reduceIte]
    rfl
  have he : QueryBits.exponent (payload p) ≠ [true] := by
    intro he
    simp [needsEntry, hd, ht, he] at hr
  simp only [step, nextState, hd, ht, ↓reduceIte, evalNext, he]
  rfl

theorem resumeEntry_eq_step (ops : Callbacks) (output : List Bool → List Bool)
    (p u : List Bool) (hr : needsEntry p = true)
    (ho : output u = ops.entry (entryInput p)) :
    resumeEntry output (pair p u) = step ops p := by
  have hd : (pairSnd p)[0]?.getD false ≠ true := by
    intro hd
    simp [needsEntry, hd] at hr
  have ht : (pairSnd p)[1]?.getD false ≠ true := by
    intro ht
    simp [needsEntry, hd, ht] at hr
  have he : QueryBits.exponent (payload p) = [true] := by
    simpa only [needsEntry, hd, ht, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] using hr
  simp only [resumeEntry, pairFst_pair, pairSnd_pair, ho, step, nextState, hd, ht,
    Bool.false_eq_true, ↓reduceIte, evalNext, he, List.cons_ne_nil, ↓reduceIte, entryInput]

theorem stepEvaluator (ops : Callbacks) (hops : ops.ControlsPolyTime)
    (E : SpaceFunction ops.entry) : SpaceFunction (step ops) := by
  let R := (E.precompose entryInput entryInput_mem_FP).withInput.postcompose
    (resumeEntry id) (resumeEntry_mem_FP id_mem_FP)
  let B := SpaceFunction.branch needsEntry needsEntry_mem_FP R
    (SpaceFunction.ofFP (step (withoutEntry ops)) (step_mem_FP _ (withoutEntry_polyTime ops hops)))
  refine B.congr (funext fun p => ?_)
  change (if needsEntry p then resumeEntry id (pair p (ops.entry (entryInput p)))
    else step (withoutEntry ops) p) = step ops p
  cases hr : needsEntry p
  · simp only [Bool.false_eq_true, reduceIte]
    exact step_withoutEntry ops p hr
  · simp only [reduceIte]
    exact resumeEntry_eq_step ops id p _ hr rfl

end LeanCanny.Algebra.MatrixPower.Controller
