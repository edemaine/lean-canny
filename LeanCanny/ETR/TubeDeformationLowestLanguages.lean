/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationLowestSpace

/-! # PSPACE tests for the computed lowest deformation coefficient

These predicates use the symbolic lowest coefficient, with its index computed
by whole-coefficient identity tests. No chosen deformation index is supplied
by the caller, and no additional coefficient or sign oracle is assumed.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open LeanCanny.Encoding.Brackets

attribute [local irreducible] RationalSubstitutionBits.compiledTerm lowestScalar

def lowestZeroLanguage (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) : Language :=
  {c | lowestScalar source active inner middle n d ell c = 0}

def lowestNegativeLanguage (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) : Language :=
  {c | lowestScalar source active inner middle n d ell c < 0}

def lowestPositiveLanguage (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) : Language :=
  {c | 0 < lowestScalar source active inner middle n d ell c}

theorem lowestZeroDecider {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceDecider (lowestZeroLanguage source active inner middle n d ell) := by
  have hf := (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  refine (lowestSignEvaluator D).decider (fun w => decide (w = [])) hf ?_
  intro c
  by_cases hz : lowestScalar source active inner middle n d ell c = 0 <;>
    by_cases hn : lowestScalar source active inner middle n d ell c < 0 <;>
    simp [lowestZeroLanguage, lowestSign, hz, hn]

theorem lowestZeroLanguage_mem_PSPACE {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) : lowestZeroLanguage source active inner middle n d ell ∈ PSPACE :=
  (lowestZeroDecider D).mem_PSPACE

theorem lowestNegativeLanguage_mem_PSPACE {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) : lowestNegativeLanguage source active inner middle n d ell ∈ PSPACE := by
  have hf := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  apply ((lowestSignEvaluator D).decider (fun w => decide (w = [true])) hf ?_).mem_PSPACE
  intro c
  by_cases hz : lowestScalar source active inner middle n d ell c = 0 <;>
    by_cases hn : lowestScalar source active inner middle n d ell c < 0 <;>
    simp [lowestNegativeLanguage, lowestSign, hz, hn]

theorem lowestPositiveLanguage_mem_PSPACE {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) : lowestPositiveLanguage source active inner middle n d ell ∈ PSPACE := by
  have hf := (stringEq_fppred id_mem_FP (constFn_mem_FP [false, true])).flag_mem_FP
  apply ((lowestSignEvaluator D).decider (fun w => decide (w = [false, true])) hf ?_).mem_PSPACE
  intro c
  by_cases hz : lowestScalar source active inner middle n d ell c = 0 <;>
    by_cases hn : lowestScalar source active inner middle n d ell c < 0 <;>
    simp [lowestPositiveLanguage, lowestSign, hz, hn] <;> omega

end LeanCanny.ETR.TubeDeformation
