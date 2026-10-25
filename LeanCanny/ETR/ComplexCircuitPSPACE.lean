/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexCircuitCompiler
public import LeanCanny.ETR.CoercivePSPACE
public import LeanCanny.Computation.SpaceDeciderFunction
public import LeanCanny.Computation.SpaceFunctionComposition

/-! # Native polynomial-space tests for complex arithmetic networks

The explicit polynomial-time gate compiler feeds the completed ETR decision
procedure. Both feasibility and emptiness have native space certificates and
agree with complex assignments on every encoded network, including networks
with shared wires and cycles.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit
open LeanCanny.Computation
open LeanCanny.Encoding.Brackets
open scoped Classical

noncomputable def feasible (bits : List Bool) : List Bool := [decide (compile bits ∈ EquationList.language)]
noncomputable def empty (bits : List Bool) : List Bool := [decide (compile bits ∉ EquationList.language)]

theorem feasible_evaluator : SpaceFunction feasible := by
  have hEq : EquationList.language ∈ PSPACE := ETR.existsReal_subset_PSPACE EquationList.mem_existsReal
  have E := (SpaceDecider.ofPSPACE hEq).flagEvaluator.precompose compile compile_mem_FP
  exact E.congr (funext fun _ => rfl)

theorem empty_evaluator : SpaceFunction empty := by
  let negate := fun bits : List Bool => [decide (bits ≠ [true])]
  have hn : negate ∈ FP := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  have E := feasible_evaluator.postcompose negate hn
  apply E.congr
  funext bits
  by_cases h : compile bits ∈ EquationList.language <;> simp [Function.comp_apply, feasible, empty, negate, h]

theorem feasible_encode (gates : List Gate) : feasible (encode gates) = [decide (Satisfiable gates)] := by
  simp only [feasible, compile_encode_correct]

theorem empty_encode (gates : List Gate) : empty (encode gates) = [decide (¬ Satisfiable gates)] := by
  simp only [empty, compile_encode_correct]

/-- Generated canonical gate queries retain the cost of both construction
and complex feasibility testing. -/
theorem feasible_generated {query : List Bool → List Gate}
    (hq : (fun bits => encode (query bits)) ∈ FP) :
    SpaceFunction (fun bits => [decide (Satisfiable (query bits))]) :=
  (feasible_evaluator.precompose _ hq).congr (funext fun bits => feasible_encode (query bits))

theorem empty_generated {query : List Bool → List Gate}
    (hq : (fun bits => encode (query bits)) ∈ FP) :
    SpaceFunction (fun bits => [decide (¬ Satisfiable (query bits))]) :=
  (empty_evaluator.precompose _ hq).congr (funext fun bits => empty_encode (query bits))

end LeanCanny.ETR.ComplexCircuit
