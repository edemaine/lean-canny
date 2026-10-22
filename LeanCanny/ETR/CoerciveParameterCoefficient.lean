/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.CoerciveNodeCoefficient
public import LeanCanny.ETR.CoerciveTableCorrectness

/-! # Native coefficients of the actual prepared coercive primitive parameter -/
@[expose] public section
namespace LeanCanny.ETR.CoerciveParameterCoefficient
open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Algebra
open SymbolicFixedTableEntryBits
open CoerciveSourceSampling

theorem nodeEvaluator : SpaceFunction (coefficient
    (SymbolicFixedTablePolynomialTree.node CoerciveFormalLeafReader.leaf)) :=
  CoerciveNodeCoefficient.evaluator

noncomputable def nodeInput (bits : List Bool) : List Bool :=
  BalancedParameterContext.packet (CoerciveIntegerPreparation.tablePrepare bits)
    (CoerciveTableCorrectness.height bits) 0

noncomputable def nodeFrame (q : List Bool) : List Bool :=
  BalancedParameterContext.packet (pairSnd q) ((dimension (pairFst q) + 1).size) 0

theorem nodeFrame_FP : nodeFrame ∈ FP := by
  have hh : UnaryFn (fun q => (dimension (pairFst q) + 1).size) :=
    ((dimension_unary.comp pairFst_mem_FP).add (UnaryFn.const 1)).size
  exact BalancedParameterContext.packet_FP pairSnd_mem_FP hh (BinaryFn.const 0)

theorem nodeInputEvaluator : SpaceFunction nodeInput :=
  (CoerciveIntegerPreparation.tablePrepareEvaluator.withInput.postcompose nodeFrame nodeFrame_FP).congr
    (funext fun bits => by
      simp only [Function.comp_apply, nodeFrame, nodeInput, pairFst_pair, pairSnd_pair,
        CoerciveTableCorrectness.height])

noncomputable def query (q : List Bool) : List Bool :=
  pair (pair (nodeInput (pairFst (pairFst q))) (pairSnd (pairFst q))) (pairSnd q)

theorem queryEvaluator : SpaceFunction query :=
  (((nodeInputEvaluator.precompose (fun q => pairFst (pairFst q))
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).pairOutputs
      (SpaceFunction.ofFP _ (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))).pairOutputs
        (SpaceFunction.ofFP _ pairSnd_mem_FP)).congr (funext fun _ => rfl)

theorem nodeInput_eq (bits : List Bool) :
    SymbolicFixedTablePolynomialTree.node CoerciveFormalLeafReader.leaf (nodeInput bits) =
      (CoercivePreparationControls.family bits).parameter := by
  rw [nodeInput, SymbolicFixedTablePolynomialTree.node_packet, CoerciveTableCorrectness.tree_eq_parameter]

theorem evaluator : SpaceFunction (coefficient (fun bits => (CoercivePreparationControls.family bits).parameter)) := by
  refine (queryEvaluator.chain nodeEvaluator).congr (funext fun q => ?_)
  simp only [Function.comp_apply, query, coefficient, pairFst_pair, pairSnd_pair, nodeInput_eq]

end LeanCanny.ETR.CoerciveParameterCoefficient
