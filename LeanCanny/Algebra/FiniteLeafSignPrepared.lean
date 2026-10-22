/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteLeafSignSource

/-! # Context reindexing for streamed finite-root sign constraints -/

@[expose] public section
namespace LeanCanny.Algebra.FiniteLeafSignBits
open LeanCanny.Encoding LeanCanny.Computation

noncomputable def Source.precompose {arity : List Bool → ℕ} (S : Source arity)
    (f : List Bool → List Bool) : Source (fun c => arity (f c)) where
  count c := S.count (f c)
  terms c := S.terms (f c)
  degree c := S.degree (f c)
  height c := S.height (f c)
  coefficient c := S.coefficient (f c)
  exponent c := S.exponent (f c)
  pattern c := S.pattern (f c)
  exponent_le c := S.exponent_le (f c)
  coefficient_le c := S.coefficient_le (f c)

def rowQuery (f : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (f (pairFst q)) (pairSnd q)

theorem rowQuery_FP (f : List Bool → List Bool) (hf : f ∈ FP) : rowQuery f ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP

def coefficientSourceQuery (f : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (pair (rowQuery f (pairFst (pairFst p))) (pairSnd (pairFst p))) (pairSnd p)

theorem coefficientSourceQuery_FP (f : List Bool → List Bool) (hf : f ∈ FP) : coefficientSourceQuery f ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (rowQuery_FP f hf))
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

def exponentSourceQuery (f : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (rowQuery f (pairFst p)) (pairSnd p)

theorem exponentSourceQuery_FP (f : List Bool → List Bool) (hf : f ∈ FP) : exponentSourceQuery f ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP (rowQuery_FP f hf)) pairSnd_mem_FP

noncomputable def Source.Access.precompose {arity : List Bool → ℕ} {S : Source arity}
    (A : S.Access) (f : List Bool → List Bool) (hf : f ∈ FP) : (S.precompose f).Access where
  coefficient := A.coefficient ∘ coefficientSourceQuery f
  exponent := A.exponent ∘ exponentSourceQuery f
  pattern := A.pattern ∘ rowQuery f
  count_unary := A.count_unary.comp hf
  terms_binary := A.terms_binary.comp hf
  degree_binary := A.degree_binary.comp hf
  height_binary := A.height_binary.comp hf
  coefficientEvaluator := A.coefficientEvaluator.precompose _ (coefficientSourceQuery_FP f hf)
  exponent_FP := mem_FP_comp (exponentSourceQuery_FP f hf) A.exponent_FP
  pattern_FP := mem_FP_comp (rowQuery_FP f hf) A.pattern_FP
  coefficient_eq q r hr m hm := by
    simpa only [Function.comp_apply, coefficientSourceQuery, rowQuery, pairFst_pair, pairSnd_pair,
      Source.precompose] using A.coefficient_eq (rowQuery f q) r (by simpa only [rowQuery, pairFst_pair, Source.precompose] using hr) m hm
  exponent_eq q r hr i hi := by
    simpa only [Function.comp_apply, exponentSourceQuery, rowQuery, pairFst_pair, pairSnd_pair,
      Source.precompose] using A.exponent_eq (rowQuery f q) r (by simpa only [rowQuery, pairFst_pair, Source.precompose] using hr) i (by simpa only [rowQuery, pairFst_pair] using hi)
  pattern_eq c j := by
    simpa only [Function.comp_apply, rowQuery, pairFst_pair, pairSnd_pair, Source.precompose] using A.pattern_eq (f c) j

end LeanCanny.Algebra.FiniteLeafSignBits
