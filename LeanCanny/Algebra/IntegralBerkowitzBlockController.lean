/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBerkowitzBlockEntry
public import LeanCanny.Computation.ControllerRequests

/-! # One-request relative Berkowitz factor selection

Unit and zero blocks are local. Diagonal blocks request one original
matrix entry, while moment blocks request one augmented block-power task.
The controller's local certificate assumes neither child evaluator.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBerkowitzBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] selector negative oneWord IntegralBlockMomentBits.Family.value

def request (S : Source) (p : List Bool) : Prop :=
  selector S p = [false, true] ∨ selector S p = [true, true]

def child (S : Source) (diagonalTask momentTask : List Bool → List Bool) (p : List Bool) : List Bool :=
  if selector S p = [false, true] then diagonalTask (diagonalQuery S p) else momentTask p

def immediate (S : Source) (p : List Bool) : List Bool :=
  if selector S p = [true] then oneWord S p else []

noncomputable def program (S : Source) (diagonalTask momentTask : List Bool → List Bool) : SingleCall.Program where
  request p := decide (request S p)
  query := child S diagonalTask momentTask
  immediate := immediate S
  finish := negative S

theorem request_FP (S : Source) (a : Access S) : FPPred (request S) :=
  (stringEq_fppred (selector_FP S a) (constFn_mem_FP [false, true])).or
    (stringEq_fppred (selector_FP S a) (constFn_mem_FP [true, true]))

theorem program_controls (S : Source) (a : Access S) (diagonalTask momentTask : List Bool → List Bool)
    (hd : diagonalTask ∈ FP) (hm : momentTask ∈ FP) : (program S diagonalTask momentTask).Controls where
  request := (request_FP S a).flag_mem_FP
  query := (stringEq_fppred (selector_FP S a) (constFn_mem_FP [false, true])).ite_mem_FP
    (mem_FP_comp (f := diagonalQuery S) (g := diagonalTask) (diagonalQuery_FP S a) hd) hm
  immediate := (stringEq_fppred (selector_FP S a) (constFn_mem_FP [true])).ite_mem_FP
    (oneWord_FP S a) (constFn_mem_FP [])
  finish := negative_FP S a


theorem program_value (S : Source) (a : Access S) (diagonalTask momentTask answer : List Bool → List Bool)
    (hd : ∀ p, selector S p = [false, true] → answer (diagonalTask (diagonalQuery S p)) = a.entry (diagonalQuery S p))
    (hm : ∀ p, selector S p = [true, true] → answer (momentTask p) = (momentFamily S).value p)
    (p : List Bool) : (program S diagonalTask momentTask).value answer p = factorValue S a p := by
  change (if decide (request S p) then negative S (pair p (answer (child S diagonalTask momentTask p)))
    else immediate S p) = factorValue S a p
  by_cases hu : selector S p = [true]
  · have hn : ¬ request S p := by rw [request, hu]; decide
    rw [show decide (request S p) = false from decide_eq_false hn]
    simp only [Bool.false_eq_true, ite_false, immediate, factorValue, hu, ite_true]
  · by_cases hd' : selector S p = [false, true]
    · have hn : request S p := Or.inl hd'
      rw [show decide (request S p) = true from decide_eq_true hn]
      simp only [ite_true]
      unfold child
      rw [ite_eq_left hd', hd p hd']
      unfold factorValue
      rw [ite_eq_right hu, ite_eq_left hd']
    · by_cases hm' : selector S p = [true, true]
      · have hn : request S p := Or.inr hm'
        rw [show decide (request S p) = true from decide_eq_true hn]
        simp only [ite_true]
        unfold child
        rw [ite_eq_right hd', hm p hm']
        unfold factorValue
        rw [ite_eq_right hu, ite_eq_right hd', ite_eq_left hm']
      · have hn : ¬ request S p := by simp only [request, hd', hm', or_self, not_false_eq_true]
        rw [show decide (request S p) = false from decide_eq_false hn]
        simp only [Bool.false_eq_true, ite_false, immediate, factorValue, hu, hd', hm']

theorem program_requests_iff (S : Source) (diagonalTask momentTask answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (p q : List Bool) :
    (program S diagonalTask momentTask).controller.Requests answer budget p q ↔
      request S p ∧ q = child S diagonalTask momentTask p := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

noncomputable def entryController (S : Source) (diagonalTask momentTask : List Bool → List Bool) : SingleCall.Program where
  request q := (program S diagonalTask momentTask).request (outerPacket S q)
  query q := (program S diagonalTask momentTask).query (outerPacket S q)
  immediate q := (program S diagonalTask momentTask).immediate (outerPacket S q)
  finish z := negative S (pair (outerPacket S (pairFst z)) (pairSnd z))

theorem entryController_controls (S : Source) (a : Access S) (diagonalTask momentTask : List Bool → List Bool)
    (hd : diagonalTask ∈ FP) (hm : momentTask ∈ FP) : (entryController S diagonalTask momentTask).Controls := by
  have H := program_controls S a diagonalTask momentTask hd hm
  have HR := mem_FP_comp (f := outerPacket S) (g := fun p => [(program S diagonalTask momentTask).request p]) (outerPacket_FP S a) H.request
  have HQ := mem_FP_comp (f := outerPacket S) (g := (program S diagonalTask momentTask).query) (outerPacket_FP S a) H.query
  have HI := mem_FP_comp (f := outerPacket S) (g := (program S diagonalTask momentTask).immediate) (outerPacket_FP S a) H.immediate
  have HF := mem_FP_comp
    (mem_FP_pair (mem_FP_comp (f := pairFst) (g := outerPacket S) pairFst_mem_FP (outerPacket_FP S a)) pairSnd_mem_FP)
    (negative_FP S a)
  exact ⟨HR, HQ, HI, HF⟩

theorem entryController_value (S : Source) (a : Access S) (diagonalTask momentTask answer : List Bool → List Bool)
    (hd : ∀ p, selector S p = [false, true] → answer (diagonalTask (diagonalQuery S p)) = a.entry (diagonalQuery S p))
    (hm : ∀ p, selector S p = [true, true] → answer (momentTask p) = (momentFamily S).value p)
    (q : List Bool) : (entryController S diagonalTask momentTask).value answer q = entryProgram S a q := by
  have H := program_value S a diagonalTask momentTask answer hd hm (outerPacket S q)
  simpa only [SingleCall.Program.value, entryController, program, pairFst_pair, pairSnd_pair,
    entryProgram, Function.comp_apply] using H

theorem entryController_packet (S : Source) (a : Access S) (diagonalTask momentTask answer : List Bool → List Bool)
    (hd : ∀ p, selector S p = [false, true] → answer (diagonalTask (diagonalQuery S p)) = a.entry (diagonalQuery S p))
    (hm : ∀ p, selector S p = [true, true] → answer (momentTask p) = (momentFamily S).value p)
    (c : List Bool) (i j : Fin (powerDimension S c)) :
    (entryController S diagonalTask momentTask).value answer
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
        residueBits ((S.powerMatrix c i j : ℤ) : ZMod (S.modulus c)) :=
  (entryController_value S a diagonalTask momentTask answer hd hm _).trans (entry_correct S a c i j)

end LeanCanny.Algebra.IntegralBerkowitzBlockBits
