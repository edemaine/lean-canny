/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

Adapted for lean-canny from TauCeti at revision 034e577c895d28c058d92af4036f7ce0b03081cf.
Source: Algebra/Polynomial/Sturm/Sequence.lean.
Changes: selected proof slice, project namespace, real specialization where needed,
and compatibility with the pinned Mathlib. See STURM_SOURCES.md.
-/
module

public import Mathlib.Algebra.Polynomial.Sturm.Sequence

/-! # Reading the second entry of a signed remainder sequence
-/

public section

namespace LeanCanny.Algebra.Sturm

open Polynomial List

section

variable {K : Type*} [Field K] [DecidableEq K]

/-- A nonzero-headed Sturm sequence has its second input as its second entry,
with zero representing the missing entry of a singleton sequence. -/
@[simp, grind =]
theorem getD_getElem?_sturmSeq {p : K[X]} (hp : p ≠ 0) (q : K[X]) :
    (sturmSeq p q)[1]?.getD 0 = q := by
  rw [← List.head?_tail]
  rw [sturmSeq_cons hp, List.tail_cons]
  by_cases hq : q = 0
  · simp only [hq, sturmSeq_zero_left, List.head?_nil, Option.getD_none]
  · simp only [head?_sturmSeq hq, Option.getD_some]

end

end LeanCanny.Algebra.Sturm
