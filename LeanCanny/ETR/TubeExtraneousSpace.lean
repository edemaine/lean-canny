/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeExtraneousModular
public import LeanCanny.ETR.TubeDeformationSpace

/-! # Complete polynomial-space tube extraneous coefficient evaluation

The FP unreduced-row selector masks the original tube coefficient reader.
Every original reader cost is included in the resulting principal determinant
computation; no enumeration of the selected principal index subtype is needed.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeExtraneous
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Algebra.RationalSubstitution

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree TubeBivariate.sourceValue
attribute [local irreducible] MacaulayBits.entryWithIdentity PolynomialMoment.augmentedInput
attribute [local irreducible] PolynomialAffineEntryBits.value BerkowitzAffinePolynomial.Family.value
attribute [local irreducible] Macaulay.matrix Matrix.det
attribute [local irreducible] TubeIndexed.degreeBound TubeParameter.spatialCount TubeCleared.matrixWidth

theorem originalEntryEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceFunction (PolynomialPrincipalBits.entry (MacaulayBits.extraneousEntry (TubeCleared.layout source))
      (TubeDeformation.originalAccess source active modulus inner middle n d ell D.bounds).modulus
      (TubeDeformation.originalAccess source active modulus inner middle n d ell D.bounds).entry) := by
  let a := TubeDeformation.originalAccess source active modulus inner middle n d ell D.bounds
  have hM' : a.modulus ∈ FP := (TubeDeformation.originalControls D).modulus
  exact PolynomialPrincipalBits.evaluator (MacaulayBits.extraneousEntry_fppred (TubeCleared.layout_polyTime D.sourceFP))
    hM' (TubeDeformation.originalEntryEvaluator D)

theorem familyEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) (outer : List Bool → List Bool) (ho : outer ∈ FP) :
    SpaceFunction (family source active modulus inner middle outer n d ell D.bounds).value := by
  have controls := TubeDeformation.originalControls D
  have hEntryBound := mem_FP_comp (TubeDeformation.entryDegreeCode_mem_FP D.sourceFP D.bounds.degreeFP) BinaryNat.normalize_mem_FP
  have hOuter := mem_FP_comp ho BinaryNat.normalize_mem_FP
  let b := access source active modulus inner middle outer n d ell D.bounds
  have hN' : b.original.dimension ∈ FP := controls.dimension
  have hM' : b.original.modulus ∈ FP := controls.modulus
  have hB' : b.bound ∈ FP := mem_FP_of_eq hEntryBound (fun _ => rfl)
  have hI' : b.inner ∈ FP := controls.degree
  have hO' : b.outer ∈ FP := mem_FP_of_eq hOuter (fun _ => rfl)
  exact b.evaluator hN' hM' hB' hI' hO' (originalEntryEvaluator D)

noncomputable def modularValue (source active modulus inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  IntegerBits.coefficientResidue (coefficient source active inner middle outer n d ell c) (Nat.fromBitsLE (modulus c) + 1)

attribute [local irreducible] coefficient

theorem evaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) (outer : List Bool → List Bool) (ho : outer ∈ FP) :
    SpaceFunction (modularValue source active modulus inner middle outer n d ell) := by
  have ES := familyEvaluator D outer ho
  have EB := SpaceFunction.branch
    (fun c => decide (Nat.fromBitsLE (inner c) < TubeDeformation.radix source D.bounds.degree c))
    (TubeDeformation.valid_fppred D).flag_mem_FP
    ES (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine EB.congr (funext fun c => ?_)
  simp only [decide_eq_true_eq]
  split_ifs with hi
  · change Nat.fromBitsLE (inner c) < TubeDeformation.radix source D.bounds.degree c at hi
    exact family_value source active modulus inner middle outer n d ell D.bounds c hi
  · change ¬Nat.fromBitsLE (inner c) < TubeDeformation.radix source D.bounds.degree c at hi
    rw [modularValue, coefficient_zero_of_not_lt source active inner middle outer n d ell D.bounds c hi]
    simp [IntegerBits.coefficientResidue, Algebra.MatrixPower.residueBits, BinaryNatCode.encode]

end LeanCanny.ETR.TubeExtraneous
