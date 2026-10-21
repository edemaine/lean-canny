/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SylvesterSpaceAccess
public import LeanCanny.Algebra.IntegerDeterminantSpaceEntries

/-! # Integer resultant zero testing with polynomial-space coefficient readers

The degree and height controls are FP. Each coefficient call may use arbitrary
time in polynomial space, including another resultant computation.
-/

@[expose] public section

namespace LeanCanny.Algebra.Resultant.Access
open LeanCanny.Computation

theorem deciderWithCoefficients {F : Family} (a : Access F) (ha : a.bits.ControlsPolyTime)
    (L : SpaceFunction a.bits.leftCoefficient) (R : SpaceFunction a.bits.rightCoefficient) :
    SpaceDecider F.zeroLanguage := by
  have h : a.integer.ControlsPolyTime := by
    constructor
    · simpa only [integer] using SylvesterBits.dimension_mem_FP_of_controls a.bits ha
    · simpa only [integer] using SylvesterBits.budget_mem_FP_of_controls a.bits ha
  exact Berkowitz.IntegerAccess.deciderWithEntry a.integer h (integer_entryEvaluator a ha L R)

end LeanCanny.Algebra.Resultant.Access
