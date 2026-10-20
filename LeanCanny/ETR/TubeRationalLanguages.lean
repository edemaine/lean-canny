/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRationalDecisions
public import LeanCanny.ETR.TubeRationalCorrect

/-! # PSPACE tests for substituted tube polynomials

The three-way infinitesimal sign decides polynomial identity and either strict
trailing-coefficient sign. Native correctness gives the corresponding eventual
rational-evaluation signs whenever coordinate denominators are nonzero.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRational
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets

attribute [local irreducible] RationalSubstitutionBits.compiledTerm Algebra.RationalSubstitution.IntegerBits.Family.polynomial

theorem polynomialZeroLanguage_mem_PSPACE (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) (B : CoordinateBounds projection source n d)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    {c | (family projection source active row n d).polynomial c = 0} ∈ PSPACE := by
  have hflag : (fun w : List Bool => [decide (w = [])]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  apply ((signEvaluator projection source active row n d C B hs ha hr).decider (fun w => decide (w = [])) hflag ?_).mem_PSPACE
  intro c
  rw [decide_eq_true_eq, Algebra.InfinitesimalSign.tag_eq_nil, Polynomial.trailingCoeff_eq_zero]
  rfl

theorem negativeLanguage_mem_PSPACE (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) (B : CoordinateBounds projection source n d)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    {c | ((family projection source active row n d).polynomial c).trailingCoeff < 0} ∈ PSPACE := by
  have hflag : (fun w : List Bool => [decide (w = [true])]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  apply ((signEvaluator projection source active row n d C B hs ha hr).decider (fun w => decide (w = [true])) hflag ?_).mem_PSPACE
  intro c
  by_cases hz : ((family projection source active row n d).polynomial c).trailingCoeff = 0
  · simp [Algebra.InfinitesimalSign.tag, hz]
  · by_cases hn : ((family projection source active row n d).polynomial c).trailingCoeff < 0 <;>
      simp [Algebra.InfinitesimalSign.tag, hz, hn]

theorem positiveLanguage_mem_PSPACE (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) (B : CoordinateBounds projection source n d)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    {c | 0 < ((family projection source active row n d).polynomial c).trailingCoeff} ∈ PSPACE := by
  have hflag : (fun w : List Bool => [decide (w = [false, true])]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [false, true])).flag_mem_FP
  apply ((signEvaluator projection source active row n d C B hs ha hr).decider (fun w => decide (w = [false, true])) hflag ?_).mem_PSPACE
  intro c
  by_cases hz : ((family projection source active row n d).polynomial c).trailingCoeff = 0
  · simp [Algebra.InfinitesimalSign.tag, hz]
  · by_cases hn : ((family projection source active row n d).polynomial c).trailingCoeff < 0
    · have hp : ¬ 0 < ((family projection source active row n d).polynomial c).trailingCoeff := by omega
      simp [Algebra.InfinitesimalSign.tag, hz, hn, hp]
    · have hp : 0 < ((family projection source active row n d).polynomial c).trailingCoeff := by omega
      simp [Algebra.InfinitesimalSign.tag, hz, hn, hp]

end LeanCanny.ETR.TubeRational
