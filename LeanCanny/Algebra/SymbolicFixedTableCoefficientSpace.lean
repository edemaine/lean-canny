/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SymbolicFixedTableSourceReset
public import LeanCanny.Algebra.SymbolicFixedTableCoefficientSource
public import LeanCanny.Algebra.BerkowitzTaskWordGrowth

/-! # Native polynomial-space symbolic balanced coefficients

All source descents rebuild commonly bounded words. The four internal stages
between descents compose a polynomial growth bound a constant number of times.
The original formal symbolic leaf reader is the sole computation hypothesis.
-/
@[expose] public section
namespace LeanCanny.Algebra.SymbolicFixedTableTreeSource
open LeanCanny.Encoding LeanCanny.Computation Turing.MultiTapeTM
open Polynomial SymbolicScaledSquarefree SymbolicFixedTableEntryBits
open SymbolicFixedTableTaskRouting BerkowitzPolynomial.TaskDispatch

variable (L : List Bool → Polynomial Coefficient) (E : List Bool → ℕ)
  (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)

theorem taskWordBound_exists (hE : BinaryFn E) (A : SpaceFunction (coefficient L)) :
    ∃ K : List Bool → ℕ, UnaryFn K ∧ ∀ root q, tasks L E hL root q → q.length ≤ K root := by
  obtain ⟨R, hR, hradix⟩ := radixSizeBound_exists L E hL hE
  obtain ⟨growth, _, hext, hunary, hlocal⟩ := internal_word_growth (access L E hL) (program L E hL).controller
    (controls L E hL hE) (program_certificates L E hL hE A) (fun _ => 1) (reachable_answer_length_le L E hL)
  let base := sourceResetBound E R
  have hbase : ∀ root, root.length ≤ base root := by intro root; unfold base sourceResetBound; omega
  have hreset (root q child : List Bool) (hq : tasks L E hL root q)
      (hstep : Requests (access L E hL) (program L E hL).controller (fun _ => 1) q child)
      (hs : SelectedSource q) : child.length ≤ base root := source_request_length_le L E hL R hradix root q child hq hstep hs
  have hu (k : ℕ) : UnaryFn (fun root => growth^[k] (base root)) := by
    induction k with
    | zero => exact sourceResetBound_unary E hE R hR
    | succ k ih => simpa only [Function.iterate_succ_apply'] using hunary _ ih
  refine ⟨fun root => growth^[4] (base root), hu 4, ?_⟩
  intro root q hq
  exact bounded_words_of_source_reset (access L E hL) (program L E hL).controller (fun _ => 1)
    base hbase growth hext hlocal hreset root q hq

include hL in
theorem evaluator (hE : BinaryFn E) (A : SpaceFunction (coefficient L)) : SpaceFunction (nodeValue L) := by
  obtain ⟨K, hK, hw⟩ := taskWordBound_exists L E hL hE A
  exact evaluator_of_taskWordBound L E hL hE A K hK hw

include hL in
theorem coefficientEvaluator (hE : BinaryFn E) (A : SpaceFunction (coefficient L)) :
    SpaceFunction (coefficient (SymbolicFixedTablePolynomialTree.node L)) := by
  obtain ⟨K, hK, hw⟩ := taskWordBound_exists L E hL hE A
  exact coefficientEvaluator_of_taskWordBound L E hL hE A K hK hw

end LeanCanny.Algebra.SymbolicFixedTableTreeSource
