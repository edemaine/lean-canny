/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationCoefficientMap

/-! # Costed affine determinant evaluation from the actual tube source

The original entry evaluator is assembled from the compiled tube row reader
and the two-parameter coefficient encoding. Its suspended source costs then
feed the affine deformation controller and the complete determinant backend.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
open Complexity LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Algebra.RationalSubstitution

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree TubeBivariate.sourceValue
attribute [local irreducible] MacaulayBits.entryWithIdentity PolynomialMoment.augmentedInput
attribute [local irreducible] PolynomialAffineEntryBits.value BerkowitzAffinePolynomial.Family.value
attribute [local irreducible] Macaulay.matrix Matrix.det
attribute [local irreducible] TubeIndexed.degreeBound TubeParameter.spatialCount TubeCleared.matrixWidth

noncomputable def originalEntryEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceFunction (originalAccess source active modulus inner middle n d ell D.bounds).entry := by
  let a := TubeBivariate.access source active modulus inner middle n d ell D.bounds
  have hL := TubeCleared.layout_polyTime D.sourceFP
  have hM := mem_FP_comp D.modulusFP BinaryNat.succ_mem_FP
  have hB := mem_FP_comp (TubeCleared.uniformDegree_mem_FP D.sourceFP D.bounds.degreeFP) BinaryNat.normalize_mem_FP
  have ES := TubeBivariate.sourceEvaluator source active modulus D.direction n d ell D.coordinates
    D.sourceFP D.activeFP D.modulusFP D.directionFP D.direction_eq
  have EC := ES.precompose a.coefficientInput (a.coefficientInput_mem_FP hL hB)
  change SpaceFunction a.encoded.coefficient at EC
  have EE := a.encoded.determinantEntryEvaluator hL hM EC
  change SpaceFunction a.encoded.determinant.entry
  exact EE

attribute [local irreducible] originalEntryEvaluator

noncomputable def familyEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) (outer : List Bool → List Bool) (ho : outer ∈ FP) :
    SpaceFunction (modularFamily source active modulus inner middle outer n d ell D.bounds).value := by
  let a := TubeBivariate.access source active modulus inner middle n d ell D.bounds
  have hL := TubeCleared.layout_polyTime D.sourceFP
  have hN := MacaulayBits.dimensionCode_mem_FP hL
  have hM := mem_FP_comp D.modulusFP BinaryNat.succ_mem_FP
  have hB := mem_FP_comp (TubeCleared.uniformDegree_mem_FP D.sourceFP D.bounds.degreeFP) BinaryNat.normalize_mem_FP
  have hI := mem_FP_comp D.innerFP BinaryNat.normalize_mem_FP
  have hT := mem_FP_comp D.outerFP BinaryNat.normalize_mem_FP
  have hPacked := a.degreeCode_mem_FP hL hB hI hT
  have hEntryBound := mem_FP_comp (entryDegreeCode_mem_FP D.sourceFP D.bounds.degreeFP) BinaryNat.normalize_mem_FP
  have hOuter := mem_FP_comp ho BinaryNat.normalize_mem_FP
  let b := modularAccess source active modulus inner middle outer n d ell D.bounds
  have hN' : b.original.dimension ∈ FP := mem_FP_of_eq hN (fun _ => rfl)
  have hM' : b.original.modulus ∈ FP := mem_FP_of_eq hM (fun _ => rfl)
  have hB' : b.bound ∈ FP := mem_FP_of_eq hEntryBound (fun _ => rfl)
  have hI' : b.inner ∈ FP := mem_FP_of_eq hPacked (fun _ => rfl)
  have hO' : b.outer ∈ FP := mem_FP_of_eq hOuter (fun _ => rfl)
  exact b.evaluator hN' hM' hB' hI' hO' (originalEntryEvaluator D)

noncomputable def modularValue (source active modulus inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  IntegerBits.coefficientResidue (coefficient source active inner middle outer n d ell c) (Nat.fromBitsLE (modulus c) + 1)

attribute [local irreducible] coefficient familyEvaluator

noncomputable def evaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) (outer : List Bool → List Bool) (ho : outer ∈ FP) :
    SpaceFunction (modularValue source active modulus inner middle outer n d ell) := by
  let a := TubeBivariate.access source active modulus inner middle n d ell D.bounds
  have hL := TubeCleared.layout_polyTime D.sourceFP
  have hB := mem_FP_comp (TubeCleared.uniformDegree_mem_FP D.sourceFP D.bounds.degreeFP) BinaryNat.normalize_mem_FP
  have hI := mem_FP_comp D.innerFP BinaryNat.normalize_mem_FP
  let F := TubeBivariate.family source active modulus inner middle n d ell D.bounds
  have hV := a.valid_fppred hL hB hI
  have ES := familyEvaluator D outer ho
  have EB := SpaceFunction.branch (fun c => decide (F.inner c < F.radix c)) hV.flag_mem_FP
    ES (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine EB.congr (funext fun c => ?_)
  simp only [decide_eq_true_eq]
  split_ifs with hi
  · change Nat.fromBitsLE (inner c) < radix source D.bounds.degree c at hi
    exact family_value source active modulus inner middle outer n d ell D.bounds c hi
  · change ¬Nat.fromBitsLE (inner c) < radix source D.bounds.degree c at hi
    rw [modularValue, coefficient_zero_of_not_lt source active inner middle outer n d ell D.bounds c hi]
    simp [IntegerBits.coefficientResidue, Algebra.MatrixPower.residueBits, BinaryNatCode.encode]

end LeanCanny.ETR.TubeDeformation
