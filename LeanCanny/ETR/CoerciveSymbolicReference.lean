/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveSymbolicSampling
public import LeanCanny.Algebra.ParameterizedSignAcceptance

/-! # A single effective symbolic sign reference for every encoded ETR input -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveSymbolicReference
open LeanCanny.Algebra CoercivePreparationControls CoerciveSymbolicSampling
open Polynomial SymbolicScaledSquarefree
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det Macaulay.fullMatrix

noncomputable def reference (bits : List Bool) : ℝ :=
  InfinitesimalSign.dyadic (ParameterTarski.patternBudget (family bits).parameter (clearedQuery bits) + 1)

theorem accepted_iff (bits : List Bool) (s : ℝ) :
    ParameterTarski.Accepted (family bits).parameter (clearedQuery bits) (accepts bits) s ↔ Realizes bits s := by
  simp only [ParameterTarski.Accepted, Polynomial.eval_map, Realizes]
  rfl

theorem correct (bits : List Bool) : bits ∈ ETR.language ↔ Realizes bits (reference bits) := by
  rw [CoerciveSymbolicSampling.correct]
  have h := ParameterTarski.eventually_accepted_iff_reference (family bits).parameter (parameter_ne_zero bits)
    (clearedQuery bits) (accepts bits)
  simpa only [EventuallyRealizes, accepted_iff, reference] using h

end LeanCanny.ETR.CoerciveSymbolicReference
