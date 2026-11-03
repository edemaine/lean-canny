/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.SquareSampleCompleteSuffixPolynomialTest
/-! # Reindexing test polynomials while keeping a complete sampler fixed

Only the indexed integer-polynomial metadata moves. The complete terminal
sampler, its vertex word and joint tuple remain those of the target input.
A count equality aligns the suffix layout; no sampler naturality or new
coefficient evaluator is assumed.
-/
@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteSuffixPolynomialTest
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Source.reindex {F G : SquareSampleInput.Inputs} (S : Source F)
    (index : List Bool→List Bool)
    (hc : ∀ c d,F.count (pairFst (index (pair c d)))=G.count c) : Source G where
  arity c d:=S.arity (pairFst (index (pair c d))) (pairSnd (index (pair c d)))
  newer c d:=S.newer (pairFst (index (pair c d))) (pairSnd (index (pair c d)))
  polynomial c d:=S.polynomial (pairFst (index (pair c d))) (pairSnd (index (pair c d)))
  degree c d:=S.degree (pairFst (index (pair c d))) (pairSnd (index (pair c d)))
  mass c d:=S.mass (pairFst (index (pair c d))) (pairSnd (index (pair c d)))
  dimension c d:=(S.dimension _ _).trans (hc c d)
  polynomial_degree _c _d:=S.polynomial_degree _ _
  polynomial_mass _c _d:=S.polynomial_mass _ _

def reindexQuery (index : List Bool→List Bool) (q : List Bool) :=
  let z:=RationalSubstitution.IntegerBits.context q
  pair (pair (index (pair (pairFst z) (pairSnd z))) (RationalSubstitution.IntegerBits.selectedDegree q)) (pairSnd q)

theorem reindexQuery_FP (index : List Bool→List Bool) (hi : index∈FP) : reindexQuery index∈FP :=
  mem_FP_pair (mem_FP_pair
    (mem_FP_comp (mem_FP_pair
      (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP)
      (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP)) hi)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP

theorem reindex_coefficient {F G : SquareSampleInput.Inputs} (S : Source F)
    (index : List Bool→List Bool) (hc : ∀ c d,F.count (pairFst (index (pair c d)))=G.count c) (q : List Bool) :
    coefficient S (reindexQuery index q)=coefficient (S.reindex index hc) q := by
  unfold coefficient reindexQuery
  simp only [RationalSubstitution.IntegerBits.context,RationalSubstitution.IntegerBits.selectedDegree,pairFst_pair,pairSnd_pair]
  rfl

theorem Source.Access.reindex {F G : SquareSampleInput.Inputs} {S : Source F} (A : S.Access)
    (index : List Bool→List Bool) (hi : index∈FP)
    (hc : ∀ c d,F.count (pairFst (index (pair c d)))=G.count c) : (S.reindex index hc).Access where
  newer := A.newer.comp (mem_FP_comp (mem_FP_pair pairFst_mem_FP pairSnd_mem_FP) hi)
  degree := A.degree.comp (mem_FP_comp (mem_FP_pair pairFst_mem_FP pairSnd_mem_FP) hi)
  mass := A.mass.comp (mem_FP_comp (mem_FP_pair pairFst_mem_FP pairSnd_mem_FP) hi)
  coefficient := (A.coefficient.precompose (reindexQuery index) (reindexQuery_FP index hi)).congr
    (funext fun q=>reindex_coefficient S index hc q)

end LeanCanny.Encoding.SquareSampleCompleteSuffixPolynomialTest
