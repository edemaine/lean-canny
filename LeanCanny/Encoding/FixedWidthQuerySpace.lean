/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FixedWidthQuery
public import LeanCanny.Computation.SpaceFunctionComposition

/-! # Fixed-width access to a space-computed record -/

@[expose] public section
namespace LeanCanny.Encoding.FixedWidthQuery
open LeanCanny.Computation

private def cachedQuery (z : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst z)) (pairSnd z)) (pairSnd (pairFst z))

private theorem cachedQuery_FP : cachedQuery ∈ FP := by
  polytime [cachedQuery]

theorem read_evaluator {A W : List Bool → ℕ} {target : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (E : SpaceFunction target) : SpaceFunction (read A W target) := by
  have H := E.call pairFst
    (read (A ∘ pairFst) (W ∘ pairFst) pairSnd ∘ cachedQuery) pairFst_mem_FP
    (mem_FP_comp cachedQuery_FP (read_mem_FP (hA.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP) pairSnd_mem_FP))
  apply H.congr
  funext q
  simp only [Function.comp_apply, cachedQuery, read, pairFst_pair, pairSnd_pair]

end LeanCanny.Encoding.FixedWidthQuery
