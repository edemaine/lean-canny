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

open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets

attribute [local irreducible] RationalSubstitutionBits.compiledTerm Algebra.RationalSubstitution.IntegerBits.Family.polynomial

theorem polynomialZeroLanguage_mem_PSPACE (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) (B : CoordinateBounds projection source n d)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    {c | (family projection source active row n d).polynomial c = 0} ∈ PSPACE := by
  have D := Algebra.IntegerSignumBits.zeroDecider_of_signum
    (fun c => ((family projection source active row n d).polynomial c).trailingCoeff)
    (signEvaluator projection source active row n d C B hs ha hr)
  apply (D.congr ?_).mem_PSPACE
  ext c
  exact Polynomial.trailingCoeff_eq_zero

theorem negativeLanguage_mem_PSPACE (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) (B : CoordinateBounds projection source n d)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    {c | ((family projection source active row n d).polynomial c).trailingCoeff < 0} ∈ PSPACE :=
  Algebra.IntegerSignumBits.negativeLanguage_of_signum
    (fun c => ((family projection source active row n d).polynomial c).trailingCoeff)
    (signEvaluator projection source active row n d C B hs ha hr)

theorem positiveLanguage_mem_PSPACE (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) (B : CoordinateBounds projection source n d)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    {c | 0 < ((family projection source active row n d).polynomial c).trailingCoeff} ∈ PSPACE :=
  Algebra.IntegerSignumBits.positiveLanguage_of_signum
    (fun c => ((family projection source active row n d).polynomial c).trailingCoeff)
    (signEvaluator projection source active row n d C B hs ha hr)

end LeanCanny.ETR.TubeRational
