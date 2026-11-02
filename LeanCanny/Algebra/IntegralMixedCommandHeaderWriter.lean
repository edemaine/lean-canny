/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCommandHeaderNative
/-! # Seven native original header readers produce the literal encoded header -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCommandHeaderBits
open LeanCanny.Encoding LeanCanny.Computation

theorem Readers.writer_FP {headers : List Bool → Header} (h : Readers headers) :
    (fun q => encode (headers q)) ∈ FP :=
  mem_FP_pair h.context.bits_mem_FP (mem_FP_pair h.coordinate.bits_mem_FP
    (mem_FP_pair h.offset.bits_mem_FP (mem_FP_pair h.objective.bits_mem_FP
      (mem_FP_pair h.degree.bits_mem_FP (mem_FP_pair h.choice.bits_mem_FP
        (mem_FP_pair h.rawTag.bits_mem_FP (constFn_mem_FP [])))))))
end LeanCanny.Algebra.IntegralMixedCommandHeaderBits
