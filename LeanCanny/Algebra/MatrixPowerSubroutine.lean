/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerControllerCorrect
public import LeanCanny.Computation.SubroutineIteration
public import LeanCanny.Computation.SubroutinePSPACE

/-!
# Matrix entry access through a suspended child evaluator

Exponent-one evaluation is intercepted before the ordinary controller step.
An FP request writer supplies context and indices to a child evaluator. Its
terminal output is installed as a return value in the retained parent stack.
Only the child's start, step, halting test, and output projection require FP
certificates; the complete entry computation need not be polynomial time.

The abstract transition contracting each completed call agrees with the original
power controller when the returned entry is correct. Actual child workspace and
clock bounds are supplied through the generic suspended-iteration interface.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower.Controller
open Complexity
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

def entryProgram (ops : Callbacks) (start advance : List Bool → List Bool)
    (halt : List Bool → Bool) (output : List Bool → List Bool) : SubroutineIteration.Program where
  ordinary := step (withoutEntry ops)
  request := needsEntry
  start := fun p => start (entryInput p)
  advance := advance
  halt := halt
  resume := resumeEntry output

theorem entryProgram_polyTime (ops : Callbacks) (hops : ops.ControlsPolyTime)
    {start advance output : List Bool → List Bool} {halt : List Bool → Bool}
    (hs : start ∈ FP) (ha : advance ∈ FP) (hh : (fun u => [halt u]) ∈ FP) (ho : output ∈ FP) :
    (entryProgram ops start advance halt output).PolyTime := by
  have hstart := mem_FP_comp entryInput_mem_FP hs
  exact ⟨step_mem_FP _ (withoutEntry_polyTime ops hops), needsEntry_mem_FP,
    hstart, ha, hh, resumeEntry_mem_FP ho⟩

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

theorem entryProgram_abstractStep (ops : Callbacks)
    (start advance : List Bool → List Bool) (halt : List Bool → Bool)
    (output : List Bool → List Bool) (T : List Bool → ℕ) (p : List Bool)
    (ho : needsEntry p = true →
      output (advance^[T p] (start (entryInput p))) = ops.entry (entryInput p)) :
    SubroutineIteration.abstractStep (entryProgram ops start advance halt output) T p = step ops p := by
  by_cases hr : needsEntry p = true
  · simp only [SubroutineIteration.abstractStep, entryProgram, hr, ↓reduceIte]
    exact resumeEntry_eq_step ops output p _ hr (ho hr)
  · have hf : needsEntry p = false := Bool.eq_false_iff.mpr hr
    simp only [SubroutineIteration.abstractStep, entryProgram, hf, Bool.false_eq_true, ↓reduceIte]
    exact step_withoutEntry ops p hf

theorem entryProgram_iterate (ops : Callbacks)
    (start advance : List Bool → List Bool) (halt : List Bool → Bool)
    (output : List Bool → List Bool) (T : List Bool → ℕ) (p : List Bool) (N : ℕ)
    (ho : ∀ k, k < N → needsEntry ((step ops)^[k] p) = true →
      output (advance^[T ((step ops)^[k] p)] (start (entryInput ((step ops)^[k] p)))) =
        ops.entry (entryInput ((step ops)^[k] p))) :
    (SubroutineIteration.abstractStep (entryProgram ops start advance halt output) T)^[N] p =
      (step ops)^[N] p := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [Function.iterate_succ_apply', ih (by intro k hk; exact ho k (by omega)),
        entryProgram_abstractStep ops start advance halt output T _ (ho N (by omega)),
        Function.iterate_succ_apply']

theorem entryProgram_run_clock (ops : Callbacks)
    (start advance : List Bool → List Bool) (halt : List Bool → Bool)
    (output : List Bool → List Bool) (T : List Bool → ℕ) (p : List Bool) (N : ℕ)
    (ho : ∀ k, k < N → needsEntry ((step ops)^[k] p) = true →
      output (advance^[T ((step ops)^[k] p)] (start (entryInput ((step ops)^[k] p)))) =
        ops.entry (entryInput ((step ops)^[k] p)))
    (hT : ∀ k, k < N → needsEntry ((step ops)^[k] p) = true →
      SubroutineIteration.TerminatesAt (entryProgram ops start advance halt output)
        ((step ops)^[k] p) (T ((step ops)^[k] p))) :
    (SubroutineIteration.step (entryProgram ops start advance halt output))^[
      SubroutineIteration.clock (entryProgram ops start advance halt output) T p N]
        (SubroutineIteration.parent p) = SubroutineIteration.parent ((step ops)^[N] p) := by
  have hiter (k : ℕ) (hk : k ≤ N) := entryProgram_iterate ops start advance halt output T p k
    (by intro j hj; exact ho j (by omega))
  rw [SubroutineIteration.iterate_clock _ T p N ?_, hiter N le_rfl]
  intro k hk
  rw [hiter k (by omega)]
  exact hT k hk

theorem needsEntry_eval {R : Type*} {n : ℕ} (c : List Bool) (enc : R → List Bool)
    (q : Query n) (stack : List (Frame R n)) :
    needsEntry (pair c (stateBits enc (.eval q stack))) = decide (q.exponent = 1) := by
  simp [needsEntry, payload, body, stateBits, exponent_queryBits]

theorem entryInput_eval {R : Type*} {n : ℕ} (c : List Bool) (enc : R → List Bool)
    (q : Query n) (stack : List (Frame R n)) :
    entryInput (pair c (stateBits enc (.eval q stack))) =
      pair c (pair (BinaryNatCode.encode q.row.val) (BinaryNatCode.encode q.col.val)) := by
  simp [entryInput, payload, body, stateBits, row_queryBits, col_queryBits]

theorem entryProgram_run_pow {R : Type*} [Semiring R] {n : ℕ}
    (ops : Callbacks) (c : List Bool) (A : Matrix (Fin n) (Fin n) R)
    (enc : R → List Bool) (hc : CorrectAt ops c A enc)
    (start advance : List Bool → List Bool) (halt : List Bool → Bool)
    (output : List Bool → List Bool) (T : List Bool → ℕ) (e : ℕ) (i j : Fin n)
    (p : List Bool) (hp : p = pair c (stateBits enc (.eval ⟨e.size, e, i, j⟩ [])))
    (ho : ∀ k, k < work n e.size e + 1 → needsEntry ((step ops)^[k] p) = true →
      output (advance^[T ((step ops)^[k] p)] (start (entryInput ((step ops)^[k] p)))) =
        ops.entry (entryInput ((step ops)^[k] p)))
    (hT : ∀ k, k < work n e.size e + 1 → needsEntry ((step ops)^[k] p) = true →
      SubroutineIteration.TerminatesAt (entryProgram ops start advance halt output)
        ((step ops)^[k] p) (T ((step ops)^[k] p))) :
    (SubroutineIteration.step (entryProgram ops start advance halt output))^[
      SubroutineIteration.clock (entryProgram ops start advance halt output) T p
        (work n e.size e + 1)] (SubroutineIteration.parent p) =
      SubroutineIteration.parent (pair c (stateBits (n := n) enc (.done ((A ^ e) i j)))) := by
  rw [entryProgram_run_clock ops start advance halt output T p _ ho hT, hp,
    Controller.run_pow ops c A enc hc]

end LeanCanny.Algebra.MatrixPower.Controller
