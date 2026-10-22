/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedTableTaskContexts
public import LeanCanny.Algebra.BerkowitzTaskWordGrowth

/-! # Uniform polynomial-space evaluation of supplied-table trees

The original leaf readers suffice. Address and degree bounds control rebuilt
matrix contexts. Decreasing internal priorities allow only four compositions
of a polynomial word-growth envelope between source descents. All graph word,
reply, metadata, and rank bounds are therefore derived on every input word.
Correct table preparation remains separate from this total evaluation theorem.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedTablePolynomials
open LeanCanny.Encoding LeanCanny.Computation Turing.MultiTapeTM
open BerkowitzPolynomial.TaskDispatch CannyBalancedTaskRouting

attribute [local irreducible] BinaryNat.normalize BinaryNat.add BinaryNat.sub BinaryNat.mul
  BinaryNat.div BinaryNat.mod tree node BalancedMetadataTable.read

theorem taskWordBound_exists (B : SeparableBits.Family) (A : SeparableBits.Readers B) :
    ∃ K : List Bool → ℕ, UnaryFn K ∧ ∀ root q, reachableTasks B root q → q.length ≤ K root := by
  let P := CannyResultantBits.WithSquarefreeLeaves.program (leafFamily B) (sourceAccess B) isLeaf
    (coefficientTask false) (coefficientTask true)
  have hC : P.controller.Certificates (encQ := encBits) (encS := SingleCall.encState) :=
    CannyResultantBits.WithSquarefreeLeaves.certificates (leafFamily B) (sourceAccess B) isLeaf
      (leafReaders B A) (source_controls B) isLeaf_FP (coefficientTask false) (coefficientTask true)
      (coefficientTask_FP false) (coefficientTask_FP true)
  have ha : (matrixAccess B).ControlsPolyTime :=
    CannyResultantBits.WithSquarefreeLeaves.controls (leafFamily B) (sourceAccess B) isLeaf (source_controls B) isLeaf_FP
  have hanswer (root q : List Bool) (hq : Reachable (matrixAccess B) P.controller (fun _ => 1) root q) :
      (answer (matrixAccess B) q).length ≤ root.length + 1 :=
    CannyBalancedTaskRouting.reachable_answer_length_le (leafFamily B) (sourceAccess B)
      (coefficient_length_le (source B).right) root q hq
  obtain ⟨growth, _, hext, hunary, hlocal⟩ := internal_word_growth (matrixAccess B) P.controller ha hC (fun _ => 1) hanswer
  let base := fun root => contextBound root + 2
  have hbase : ∀ root, root.length ≤ base root := by intro root; dsimp only [base, contextBound]; omega
  have hreset (root q child : List Bool) (hq : Reachable (matrixAccess B) P.controller (fun _ => 1) root q)
      (hstep : Requests (matrixAccess B) P.controller (fun _ => 1) q child) (hs : SelectedSource q) : child.length ≤ base root := by
    have hc : reachableTasks B root child := hq.tail hstep
    have hl := reachable_context_length_le B root child hc
    obtain ⟨_, _, he⟩ := request_source (leafFamily B) (sourceAccess B) q child hstep hs
    have heq : child.length = (origin child).length + 2 := by
      have hd (p : List Bool) : (determinantTask p).length = (origin (determinantTask p)).length + 2 := by
        rw [origin_determinant]
        simp only [determinantTask, tag, List.length_cons]
      rw [he]
      split_ifs <;> exact hd _
    dsimp only [base]
    omega
  have hu (k : ℕ) : UnaryFn (fun root => growth^[k] (base root)) := by
    induction k with
    | zero => exact contextBound_unary.add (UnaryFn.const 2)
    | succ k ih => simpa only [Function.iterate_succ_apply'] using hunary _ ih
  refine ⟨fun root => growth^[4] (base root), hu 4, ?_⟩
  intro root q hq
  exact bounded_words_of_source_reset (matrixAccess B) P.controller (fun _ => 1) base hbase growth hext hlocal hreset root q hq

/-- One native machine evaluates every supplied-table tree from the original
leaf reader alone, including inconsistent tables and malformed query words. -/
theorem evaluator (B : SeparableBits.Family) (A : SeparableBits.Readers B) : SpaceFunction (nodeValue B) := by
  obtain ⟨K, hK, hw⟩ := taskWordBound_exists B A
  exact evaluator_of_taskWordBound B A K hK hw

end LeanCanny.Algebra.BalancedTablePolynomials
