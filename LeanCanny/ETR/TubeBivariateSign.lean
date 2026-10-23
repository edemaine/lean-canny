/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeBivariateResidue
public import LeanCanny.Algebra.IntegerSignumSpace
public import LeanCanny.Algebra.IntegerZeroSpace

/-! # Integer signs of full regular tube determinant coefficients in PSPACE

The actual residue evaluator and FP coefficient budget compose with the
streamed CRT routines. Zero, negative and positive tags are `[]`, `[true]`,
and `[false,true]`. No integer coefficient or large CRT modulus is stored.
The input contracts remain those of the parameter-coordinate and direction
readers; no additional determinant or sign oracle is assumed.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeBivariate
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open LeanCanny.Encoding.Brackets

attribute [local irreducible] RationalSubstitutionBits.compiledTerm integerCoefficient integerBudget

noncomputable def integerSign (source active inner outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  if integerCoefficient source active inner outer n d ell c = 0 then []
  else if integerCoefficient source active inner outer n d ell c < 0 then [true] else [false, true]

def integerZeroLanguage (source active inner outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) : Language :=
  {c | integerCoefficient source active inner outer n d ell c = 0}

def integerNegativeLanguage (source active inner outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) : Language :=
  {c | integerCoefficient source active inner outer n d ell c < 0}

def integerPositiveLanguage (source active inner outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) : Language :=
  {c | 0 < integerCoefficient source active inner outer n d ell c}

theorem Data.signumEvaluator {source active modulus inner outer : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : Data source active modulus inner outer n d ell) : SpaceFunction (integerSign source active inner outer n d ell) := by
  have hb := integerBudget_mem_FP D.sourceFP D.directionFP D.bounds.degreeFP D.bounds.bitsFP
  exact IntegerSignumBits.evaluator D.residueEvaluator (integerBudget source D.direction D.bounds.degree D.bounds.bits) hb
    (integerCoefficient source active inner outer n d ell)
    (integerCoefficient_bits source active D.direction inner outer n d ell D.bounds D.direction_eq)
    (residue_packet source active inner outer n d ell D.bounds)

theorem Data.integerZeroDecider {source active modulus inner outer : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : Data source active modulus inner outer n d ell) : SpaceDecider (integerZeroLanguage source active inner outer n d ell) := by
  have hb := integerBudget_mem_FP D.sourceFP D.directionFP D.bounds.degreeFP D.bounds.bitsFP
  exact IntegerZeroBits.zeroDecider D.residueEvaluator (integerBudget source D.direction D.bounds.degree D.bounds.bits) hb
    (integerCoefficient source active inner outer n d ell)
    (integerCoefficient_bits source active D.direction inner outer n d ell D.bounds D.direction_eq)
    (residue_packet source active inner outer n d ell D.bounds)

theorem Data.integerZeroLanguage_mem_PSPACE {source active modulus inner outer : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : Data source active modulus inner outer n d ell) : integerZeroLanguage source active inner outer n d ell ∈ PSPACE :=
  D.integerZeroDecider.mem_PSPACE

theorem Data.integerNegativeLanguage_mem_PSPACE {source active modulus inner outer : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : Data source active modulus inner outer n d ell) : integerNegativeLanguage source active inner outer n d ell ∈ PSPACE :=
  IntegerSignumBits.negativeLanguage_of_signum
    (integerCoefficient source active inner outer n d ell) D.signumEvaluator

theorem Data.integerPositiveLanguage_mem_PSPACE {source active modulus inner outer : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : Data source active modulus inner outer n d ell) : integerPositiveLanguage source active inner outer n d ell ∈ PSPACE :=
  IntegerSignumBits.positiveLanguage_of_signum
    (integerCoefficient source active inner outer n d ell) D.signumEvaluator

end LeanCanny.ETR.TubeBivariate
