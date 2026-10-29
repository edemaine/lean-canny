/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleGrid
public import LeanCanny.Encoding.SquareSampleSquarefree
public import LeanCanny.Algebra.UnivariateRowSpace

/-! # Native regular coordinate-grid access from the original input readers -/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleGrid
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

noncomputable def selected (F : Inputs) (q : List Bool) : Fin (F.count (SquareSampleInput.source q)) :=
  SquareSampleInput.selected F (SquareSampleInput.source q) (SquareSampleInput.indexWord q)

theorem selected_unary {F : Inputs} (h : F.Access) : UnaryFn (fun q => (selected F q).val) :=
  UnaryFn.fromBitsLE_min SquareSampleInput.indexWord_FP
    ((h.count.comp SquareSampleInput.source_FP).sub (UnaryFn.const 1))

def sourceQuery (q : List Bool) := pair (SquareSampleInput.source q) (SquareSampleInput.indexWord q)

theorem sourceQuery_FP : sourceQuery ∈ FP := mem_FP_pair SquareSampleInput.source_FP SquareSampleInput.indexWord_FP

theorem row_evaluator {F : Inputs} (h : F.Access) :
    SpaceFunction (SquareSampleInput.rowCoefficient (input F)) := by
  have E := PrimitivePairBits.withContextEvaluator (SquareSampleSquarefree.polynomial F) sourceQuery
    (SpaceFunction.ofFP _ sourceQuery_FP) (SquareSampleSquarefree.evaluator h)
  have ER := UnivariateRowBits.evaluator (h.count.comp SquareSampleInput.source_FP)
    (UnaryFn.length SquareSampleInput.widthWord_FP) (selected F) (selected_unary h)
    (SquareSampleSquarefree.polynomial F ∘ sourceQuery) E SquareSampleInput.rankWord_FP SquareSampleInput.modulusWord_FP
  refine ER.congr (funext fun q => ?_)
  simp only [FixedWidthRowBits.value, Function.comp_apply, sourceQuery, SquareSampleSquarefree.polynomial_pair]
  rfl

theorem access {F : Inputs} (h : F.Access) : (input F).Access :=
  ⟨h.count, h.annDegree.add (BinaryFn.const 1), mass_binary h, h.annDegree, h.annHeight,
    row_evaluator h, h.annihilator⟩

end LeanCanny.Encoding.SquareSampleGrid
