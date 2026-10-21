/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationCharacteristic
public import LeanCanny.Algebra.SignedTagSpace
public import LeanCanny.Computation.SpaceFunctionComposition

/-! # PSPACE signs for the lowest characteristic-numerator coefficient

The computed lowest deformation index supplies the parity correction between
the affine interpolation and det(A-sI). Pairing the complete index and sign
evaluators includes both child costs; the final tag correction is FP.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
open Complexity LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open LeanCanny.Encoding.Brackets

attribute [local irreducible] RationalSubstitutionBits.compiledTerm characteristicScalar lowestScalar determinant SignedTagBits.correct

noncomputable def characteristicSign (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  InfinitesimalSign.tag (characteristicScalar source active inner middle n d ell c)

theorem characteristicSignEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceFunction (characteristicSign source active inner middle n d ell) := by
  have E := (lowestIndexEvaluator D).pairOutputs (lowestSignEvaluator D)
  have F := E.postcompose SignedTagBits.correct SignedTagBits.correct_mem_FP
  refine F.congr (funext fun c => ?_)
  change SignedTagBits.correct (pair (lowestIndex source active n d ell c)
    (InfinitesimalSign.tag (lowestScalar source active inner middle n d ell c))) =
      InfinitesimalSign.tag (characteristicScalar source active inner middle n d ell c)
  rw [lowestIndex, SignedTagBits.correct_pair, characteristicScalar_eq, lowestIndex_value]

theorem characteristicZeroDecider {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceDecider {c | characteristicScalar source active inner middle n d ell c = 0} := by
  refine (lowestZeroDecider D).congr ?_
  ext c
  exact (characteristicScalar_zero_iff source active inner middle n d ell c).symm

theorem characteristicZeroLanguage_mem_PSPACE {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    {c | characteristicScalar source active inner middle n d ell c = 0} ∈ PSPACE :=
  (characteristicZeroDecider D).mem_PSPACE

theorem characteristicNegativeLanguage_mem_PSPACE {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    {c | characteristicScalar source active inner middle n d ell c < 0} ∈ PSPACE := by
  have hf := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  apply ((characteristicSignEvaluator D).decider (fun w => decide (w = [true])) hf ?_).mem_PSPACE
  intro c
  by_cases hz : characteristicScalar source active inner middle n d ell c = 0 <;>
    by_cases hn : characteristicScalar source active inner middle n d ell c < 0 <;>
    simp [characteristicSign, InfinitesimalSign.tag, hz, hn]

theorem characteristicPositiveLanguage_mem_PSPACE {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    {c | 0 < characteristicScalar source active inner middle n d ell c} ∈ PSPACE := by
  have hf := (stringEq_fppred id_mem_FP (constFn_mem_FP [false, true])).flag_mem_FP
  apply ((characteristicSignEvaluator D).decider (fun w => decide (w = [false, true])) hf ?_).mem_PSPACE
  intro c
  by_cases hz : characteristicScalar source active inner middle n d ell c = 0 <;>
    by_cases hn : characteristicScalar source active inner middle n d ell c < 0 <;>
    simp [characteristicSign, InfinitesimalSign.tag, hz, hn] <;> omega

end LeanCanny.ETR.TubeDeformation
