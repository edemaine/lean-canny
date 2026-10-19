/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EncodedRationalSubstitution
public import LeanCanny.ETR.EquationCompilerFP

/-!
# A concrete rational-substitution source for arbitrary encoded ETR inputs

The verified FP equation compiler supplies the arithmetic source term. Every
binary input produces a well-formed term, and its real zero set is nonempty
exactly for ETR yes-instances. The complete source access interface is therefore
available for general formulas, including unsatisfiable malformed-input defaults.
Coordinate construction and algebraic-root sign determination remain separate.
-/

@[expose] public section

namespace LeanCanny.ETR.RationalSubstitutionBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets

def compiledTerm : List Bool → List Bool := NNF.second ∘ EquationCompiler.toSingleEquation

theorem compiledTerm_mem_FP : compiledTerm ∈ FP := by
  have h := mem_FP_comp EquationCompiler.toSingleEquation_mem_FP NNF.second_mem_FP
  exact h

theorem compiledTerm_shape (bits : List Bool) : ∃ t : Term,
    EquationCompiler.toSingleEquation bits = (Formula.eqZero t).encode ∧ compiledTerm bits = t.toData.toBits := by
  obtain ⟨ts, hts⟩ := EquationCompiler.compileTerms_shape bits
  have heq : EquationCompiler.toSingleEquation bits = (Formula.eqZero (SumSquares.accumulate ts (.const 0))).encode := by
    rw [EquationCompiler.toSingleEquation, hts, EquationList.toSingleEquation_listBits]
  refine ⟨_, heq, ?_⟩
  rw [compiledTerm, Function.comp_apply, heq]
  simp only [NNF.second, Formula.encode, Formula.toData, remainingChildren_toBits, firstChild_toBits]

noncomputable def compiledSource : Source := Source.ofTerm compiledTerm

theorem compiledSource_polyTime : compiledSource.PolyTime := Source.ofTerm_polyTime compiledTerm_mem_FP

theorem compiledTerm_correct (bits : List Bool) :
    bits ∈ ETR.language ↔ ∃ env : ℕ → ℝ, (TermView.term (compiledTerm bits)).eval env = 0 := by
  obtain ⟨t, heq, ht⟩ := compiledTerm_shape bits
  rw [EquationCompiler.toSingleEquation_correct, heq, SingleEquation.encode_mem_language, ht, TermView.term_toBits]
  simp only [Formula.Satisfiable, Formula.Holds]

theorem compiledSource_correct (bits : List Bool) :
    bits ∈ ETR.language ↔ ∃ env : ℕ → ℝ, (compiledSource.syntax bits).eval env = 0 := by
  simpa only [Source.syntax, compiledSource, Source.ofTerm] using compiledTerm_correct bits

end LeanCanny.ETR.RationalSubstitutionBits
