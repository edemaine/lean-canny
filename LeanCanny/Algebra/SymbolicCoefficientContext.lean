/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableEntrySpace

/-! # Native bivariate coefficient context substitution -/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicFixedTableEntryBits
open LeanCanny.Encoding LeanCanny.Computation

def contextQuery (f : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (f (pairFst (pairFst q))) (pairSnd (pairFst q))) (pairSnd q)

lemma contextQuery_FP {f : List Bool → List Bool} (hf : f ∈ FP) : contextQuery f ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hf)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

lemma withContextEvaluator (p : List Bool → Polynomial (Polynomial ℤ))
    (f : List Bool → List Bool) (hf : f ∈ FP) (P : SpaceFunction (coefficient p)) :
    SpaceFunction (coefficient (p ∘ f)) := by
  refine (P.precompose (contextQuery f) (contextQuery_FP hf)).congr (funext fun q => ?_)
  simp only [Function.comp_apply, coefficient, contextQuery, pairFst_pair, pairSnd_pair]

end LeanCanny.Algebra.SymbolicFixedTableEntryBits
