/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.EncodedTermPolynomial
public import LeanCanny.CountingHierarchy.ControlledFeasibility
public import LeanCanny.ETR.CompiledRationalSource
public import LeanCanny.ETR.Complexity

/-! # The encoded existential theory of the reals in C₂₆P

The counting-hierarchy result follows OpenAI,
*Existential–universal real sentences in the counting hierarchy* (October 4, 2026):
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/etr-counting-hierarchy.pdf
The historical `LeanCanny` namespace records the host project, not authorship.

The native equation compiler and modular tree evaluator provide the controlled
source family. The generic feasibility theorem then decides every binary input,
including malformed formulas. Polynomial-time reductions transfer the bound
to all of ∃ℝ.
-/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

attribute [local irreducible] TermEvaluation.controlled TermEvaluation.polynomial
attribute [local irreducible] ETR.RationalSubstitutionBits.compiledTerm

/-- The repository's complete encoded ETR language belongs to one fixed
counting level, without a promise of well-formedness. -/
theorem etr_mem_CountingLevel : ETR.language ∈ CountingLevel 26 encBits := by
  let source := ETR.RationalSubstitutionBits.compiledTerm
  have hs : source ∈ FP := ETR.RationalSubstitutionBits.compiledTerm_mem_FP
  have h := (TermEvaluation.controlled source hs).feasibility_mem Decoder.bits
  change {w | ∃ x : Fin (TermEvaluation.arity source w) → ℝ,
    eval x ((TermEvaluation.polynomial source w).map (Int.castRingHom ℝ)) = 0} ∈
      CountingLevel 26 encBits at h
  convert h using 1
  ext w
  rw [ETR.RationalSubstitutionBits.compiledTerm_correct]
  simpa only [Set.mem_ofPred_eq, eval_map] using (TermEvaluation.feasible_iff source w).symm

/-- Every problem in ∃ℝ has the same uniform counting-level upper bound. -/
theorem existsReal_subset_CountingLevel : ExistsReal ⊆ CountingLevel 26 encBits := by
  intro L hL
  exact hL.mem_CountingLevel etr_mem_CountingLevel

end LeanCanny.CountingHierarchy
