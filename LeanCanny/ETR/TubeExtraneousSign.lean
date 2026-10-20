/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeExtraneousResidue
public import LeanCanny.ETR.TubeExtraneousBudget

/-! # Integer signs of full tube extraneous deformation coefficients

The actual modular evaluator and proved binary coefficient budget supply the
streamed CRT sign and zero routines. All original parameter-reader workspace
is included; no deformed coefficient, determinant, or sign oracle is assumed.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeExtraneous
open Complexity LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open LeanCanny.Encoding.Brackets

attribute [local irreducible] RationalSubstitutionBits.compiledTerm coefficient TubeDeformation.budget

noncomputable def integerSign (source active inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  if coefficient source active inner middle outer n d ell c = 0 then []
  else if coefficient source active inner middle outer n d ell c < 0 then [true] else [false, true]

def integerZeroLanguage (source active inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) : Language :=
  {c | coefficient source active inner middle outer n d ell c = 0}

def integerNegativeLanguage (source active inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) : Language :=
  {c | coefficient source active inner middle outer n d ell c < 0}

def integerPositiveLanguage (source active inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) : Language :=
  {c | 0 < coefficient source active inner middle outer n d ell c}

noncomputable def signumEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) (outer : List Bool → List Bool) (ho : outer ∈ FP) :
    SpaceFunction (integerSign source active inner middle outer n d ell) := by
  have hb := TubeDeformation.budget_mem_FP D.sourceFP D.directionFP D.bounds.degreeFP D.bounds.bitsFP
  exact IntegerSignumBits.evaluator (residueEvaluator D outer ho) (TubeDeformation.budget source D.direction D.bounds.degree D.bounds.bits) hb
    (coefficient source active inner middle outer n d ell)
    (coefficient_bits source active D.direction inner middle outer n d ell D.bounds D.direction_eq)
    (residue_packet source active inner middle outer n d ell)

noncomputable def integerZeroDecider {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) (outer : List Bool → List Bool) (ho : outer ∈ FP) :
    SpaceDecider (integerZeroLanguage source active inner middle outer n d ell) := by
  have hb := TubeDeformation.budget_mem_FP D.sourceFP D.directionFP D.bounds.degreeFP D.bounds.bitsFP
  exact IntegerZeroBits.zeroDecider (residueEvaluator D outer ho) (TubeDeformation.budget source D.direction D.bounds.degree D.bounds.bits) hb
    (coefficient source active inner middle outer n d ell)
    (coefficient_bits source active D.direction inner middle outer n d ell D.bounds D.direction_eq)
    (residue_packet source active inner middle outer n d ell)

theorem integerZeroLanguage_mem_PSPACE {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) (outer : List Bool → List Bool) (ho : outer ∈ FP) :
    integerZeroLanguage source active inner middle outer n d ell ∈ PSPACE :=
  (integerZeroDecider D outer ho).mem_PSPACE

theorem integerNegativeLanguage_mem_PSPACE {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) (outer : List Bool → List Bool) (ho : outer ∈ FP) :
    integerNegativeLanguage source active inner middle outer n d ell ∈ PSPACE := by
  have hf := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  apply ((signumEvaluator D outer ho).decider (fun w => decide (w = [true])) hf ?_).mem_PSPACE
  intro c
  by_cases hz : coefficient source active inner middle outer n d ell c = 0 <;>
    by_cases hn : coefficient source active inner middle outer n d ell c < 0 <;>
    simp [integerNegativeLanguage, integerSign, hz, hn]

theorem integerPositiveLanguage_mem_PSPACE {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) (outer : List Bool → List Bool) (ho : outer ∈ FP) :
    integerPositiveLanguage source active inner middle outer n d ell ∈ PSPACE := by
  have hf := (stringEq_fppred id_mem_FP (constFn_mem_FP [false, true])).flag_mem_FP
  apply ((signumEvaluator D outer ho).decider (fun w => decide (w = [false, true])) hf ?_).mem_PSPACE
  intro c
  by_cases hz : coefficient source active inner middle outer n d ell c = 0 <;>
    by_cases hn : coefficient source active inner middle outer n d ell c < 0 <;>
    simp [integerPositiveLanguage, integerSign, hz, hn] <;> omega

end LeanCanny.ETR.TubeExtraneous
