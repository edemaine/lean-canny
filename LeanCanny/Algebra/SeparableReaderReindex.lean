/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SeparableSpace

/-! # Reindexing certified original polynomial families -/

@[expose] public section

namespace LeanCanny.Algebra.SeparableBits
open LeanCanny.Encoding LeanCanny.Computation

noncomputable def Family.reindex (F : Family) (input : List Bool → List Bool) : Family where
  polynomial c := F.polynomial (input c)
  height c := F.height (input c)
  coefficient_bound c := F.coefficient_bound (input c)

def reindexQuery (input : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (pair (input (pairFst (pairFst p))) (pairSnd (pairFst p))) (pairSnd p)

theorem reindexQuery_FP (input : List Bool → List Bool) (hi : input ∈ FP) : reindexQuery input ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hi
  have hm := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair hc hm) pairSnd_mem_FP

noncomputable def Readers.reindex {F : Family} (A : Readers F) (input : List Bool → List Bool) (hi : input ∈ FP) :
    Readers (F.reindex input) where
  degree := A.degree ∘ input
  height := A.height ∘ input
  coefficient := A.coefficient ∘ reindexQuery input
  degreeFP := mem_FP_comp hi A.degreeFP
  heightFP := mem_FP_comp hi A.heightFP
  degree_eq c := A.degree_eq (input c)
  height_eq c := A.height_eq (input c)
  coefficient_eq := by
    intro q k
    have h := A.coefficient_eq (pair (input (pairFst q)) (pairSnd q)) k
    rw [pairFst_pair, pairSnd_pair] at h
    simpa only [Family.reindex, reindexQuery, Function.comp_apply, pairFst_pair, pairSnd_pair] using h
  evaluator := A.evaluator.precompose (reindexQuery input) (reindexQuery_FP input hi)

end LeanCanny.Algebra.SeparableBits
