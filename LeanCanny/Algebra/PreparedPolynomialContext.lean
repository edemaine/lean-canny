/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairReaders
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Substituting a space-computed context into an integer coefficient reader -/

@[expose] public section

namespace LeanCanny.Algebra.PrimitivePairBits
open LeanCanny.Encoding LeanCanny.Computation
open RationalSubstitution.IntegerBits (context selectedDegree mValue)

def replaceContext (z : List Bool) : List Bool :=
  pair (pair (pairSnd z) (selectedDegree (pairFst z))) (pairSnd (pairFst z))

theorem replaceContext_FP : replaceContext ∈ FP :=
  mem_FP_pair (mem_FP_pair pairSnd_mem_FP
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP))
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

theorem withContextEvaluator (p : List Bool → Polynomial ℤ) (prepare : List Bool → List Bool)
    (P : SpaceFunction prepare) (E : SpaceFunction (coefficient p)) :
    SpaceFunction (coefficient (p ∘ prepare)) := by
  have R := ((P.precompose context RationalSubstitution.IntegerBits.context_mem_FP).withInput.postcompose
    replaceContext replaceContext_FP).chain E
  refine R.congr (funext fun q => ?_)
  simp only [Function.comp_apply, coefficient, replaceContext, context, selectedDegree, mValue,
    pairFst_pair, pairSnd_pair]

end LeanCanny.Algebra.PrimitivePairBits
