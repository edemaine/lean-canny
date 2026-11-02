/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryPositivePrefix
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptyNativeSquare
public import LeanCanny.Encoding.SquareSampleCompleteVertices

/-! # Original-only native positive-prefix sampling and vertices

The n+1 selector is positive even at n=0. Original syntax supplies the actual
row reader, so no positivity, matrix, coefficient or evaluator premise is added.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryPositivePrefix
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
variable {n : List Bool→ℕ} {t : List Bool→Term}

theorem native_access (hn : UnaryFn n) (ht : (fun u=>(t u).toData.toBits)∈FP) (ha : ∀ u,(t u).arity≤n u)
    (root : List Bool→List Bool) (hr : root∈FP) : (input hn ht ha root).Access :=
  IntegralMixedAuxiliaryEmptyPlan.square_native_access hn ht ha (key n root) (key_FP hn hr) (key_positive n t root)

theorem native_count_evaluator (hn : UnaryFn n) (ht : (fun u=>(t u).toData.toBits)∈FP) (ha : ∀ u,(t u).arity≤n u)
    (root : List Bool→List Bool) (hr : root∈FP) :
    SpaceFunction (fun u=>BinaryNatCode.encode (SquareSampleComplete.count (input hn ht ha root) u)) :=
  SquareSampleComplete.count_evaluator (native_access hn ht ha root hr) (complete hn ht ha root)

theorem vertex_width_unary (hn : UnaryFn n) (ht : (fun u=>(t u).toData.toBits)∈FP) (ha : ∀ u,(t u).arity≤n u)
    (root : List Bool→List Bool) (hr : root∈FP) : UnaryFn (SquareSampleCompleteVertices.width (input hn ht ha root)) :=
  SquareSampleCompleteVertices.width_unary (native_access hn ht ha root hr)

theorem vertices_mem_PSPACE (hn : UnaryFn n) (ht : (fun u=>(t u).toData.toBits)∈FP) (ha : ∀ u,(t u).arity≤n u)
    (root : List Bool→List Bool) (hr : root∈FP) : SquareSampleCompleteVertices.language (input hn ht ha root)∈PSPACE :=
  SquareSampleCompleteVertices.mem_PSPACE (native_access hn ht ha root hr)

end LeanCanny.Encoding.IntegralMixedAuxiliaryPositivePrefix
