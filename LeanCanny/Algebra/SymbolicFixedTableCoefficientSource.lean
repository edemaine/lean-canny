/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableTaskResidues

/-! # Uniform symbolic table evaluation from a reachable word bound

The bottom leaf coefficient reader is the only polynomial reader input.
Actual child semantics, graph closure, native metadata bounds, reply bounds,
and decreasing ranks are supplied by the concrete construction. The remaining
word bound is stated explicitly for the subsequent global size argument.
-/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicFixedTableTreeSource
open LeanCanny.Encoding LeanCanny.Computation
open Polynomial SymbolicScaledSquarefree SymbolicFixedTableEntryBits
open SymbolicFixedTableTaskRouting BerkowitzPolynomial.TaskDispatch

variable (L : List Bool → Polynomial Coefficient) (E : List Bool → ℕ)
  (hL : ∀ c i k, ((L (pair c (BinaryNatCode.encode i))).coeff k).natDegree ≤ E c)

theorem evaluator_of_taskWordBound (hE : BinaryFn E) (A : SpaceFunction (coefficient L))
    (K : List Bool → ℕ) (hK : UnaryFn K)
    (hword : ∀ root q, tasks L E hL root q → q.length ≤ K root) : SpaceFunction (nodeValue L) := by
  let K' := fun root => K root + root.length + 1
  have hK' : UnaryFn K' := (hK.add (UnaryFn.length id_mem_FP)).add (UnaryFn.const 1)
  have hw (root q : List Bool) (hq : tasks L E hL root q) : q.length ≤ K' root :=
    (hword root q hq).trans (by dsimp only [K']; omega)
  have hr (root q : List Bool) (hq : tasks L E hL root q) : (answer (access L E hL) q).length ≤ K' root :=
    (reachable_answer_length_le L E hL root q hq).trans (by dsimp only [K']; omega)
  obtain ⟨M, hM, hb⟩ := commonMetadata_bound (access L E hL) (controls L E hL hE) K' hK'
  have hp (root q : List Bool) (hq : tasks L E hL root q) : (payload q).length ≤ K' root := by
    simp only [payload, List.length_drop]
    exact (Nat.sub_le _ _).trans (hw root q hq)
  have V := singleCall_evaluator (access L E hL) (program L E hL) (controls L E hL hE)
    (program_certificates L E hL hE A) (program_correct L E hL)
    (tasks L E hL) level List.length K' M (UnaryFn.length id_mem_FP) hK' hM
    (tasks_root L E hL) (reachable_level_bound L E hL) hw hr (tasks_closed L E hL)
    (source_levels L E hL _) (fun root q hq _ => (hb root (payload q) (hp root q hq)).1)
    (fun root q hq _ => (hb root (payload q) (hp root q hq)).2)
  exact (determinant_reader (access L E hL) V).congr (funext (family_value L E hL))

def nodeCoefficientQuery (q : List Bool) : List Bool :=
  matrixPacket (pairFst (pairFst q)) (pairFst (pairSnd q)) (pairSnd (pairSnd q)) (pairSnd (pairFst q))

theorem nodeCoefficientQuery_FP : nodeCoefficientQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)))
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

theorem coefficientEvaluator_of_taskWordBound (hE : BinaryFn E) (A : SpaceFunction (coefficient L))
    (K : List Bool → ℕ) (hK : UnaryFn K)
    (hword : ∀ root q, tasks L E hL root q → q.length ≤ K root) :
    SpaceFunction (coefficient (SymbolicFixedTablePolynomialTree.node L)) := by
  refine ((evaluator_of_taskWordBound L E hL hE A K hK hword).precompose
    nodeCoefficientQuery nodeCoefficientQuery_FP).congr (funext fun q => ?_)
  simp only [Function.comp_apply, nodeCoefficientQuery, nodeValue, nodeContext, matrixPacket,
    coefficient, alpha, theta, pairFst_pair, pairSnd_pair]

end LeanCanny.Algebra.SymbolicFixedTableTreeSource
