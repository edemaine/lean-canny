/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationCoefficientMap

/-! # Costed affine determinant evaluation from the actual tube source

The original entry evaluator is assembled from the compiled tube row reader
and the two-parameter coefficient encoding. Its space-bounded source costs then
feed the affine deformation controller and the complete determinant backend.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Algebra.RationalSubstitution

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree TubeBivariate.sourceValue
attribute [local irreducible] MacaulayBits.entryWithIdentity PolynomialMoment.augmentedInput
attribute [local irreducible] PolynomialAffineEntryBits.value BerkowitzAffinePolynomial.Family.value
attribute [local irreducible] Macaulay.matrix Matrix.det
attribute [local irreducible] TubeIndexed.degreeBound TubeParameter.spatialCount TubeCleared.matrixWidth

/-- Both consumers use binary dimension and entry-degree controls. -/
theorem determinantControls {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    BinaryFn (TubeBivariate.family source active modulus inner middle n d ell D.bounds).determinant.dimension ∧
    BinaryFn (TubeBivariate.family source active modulus inner middle n d ell D.bounds).determinant.bound := by
  constructor
  · exact BinaryFn.of_bits (mem_FP_of_eq
      (MacaulayBits.dimensionCode_mem_FP (TubeCleared.layout_polyTime D.sourceFP))
      (FixedWidthPolynomial.countCode_code _ _))
  · exact BinaryFn.fromBits (TubeCleared.uniformDegree_mem_FP D.sourceFP D.bounds.degreeFP)

theorem originalEntryEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceFunction (originalAccess source active modulus inner middle n d ell D.bounds).entry := by
  let a := TubeBivariate.access source active modulus inner middle n d ell D.bounds
  let F := (TubeBivariate.family source active modulus inner middle n d ell D.bounds).determinant
  have ES := TubeBivariate.sourceEvaluator source active modulus D.direction n d ell D.coordinates
    D.sourceFP D.activeFP D.modulusFP D.directionFP D.direction_eq
  have hM := mem_FP_comp D.modulusFP BinaryNat.succ_mem_FP
  have EE := a.entryEvaluator (TubeCleared.layout_polyTime D.sourceFP) hM ES
  exact F.encodedEntryEvaluator a.entry a.entry_correct
    (determinantControls D).1 (determinantControls D).2 EE

theorem originalControls {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    (originalAccess source active modulus inner middle n d ell D.bounds).ControlsPolyTime := by
  let F := (TubeBivariate.family source active modulus inner middle n d ell D.bounds).determinant
  exact ⟨(determinantControls D).1.bits_mem_FP,
    ((BinaryFn.fromBits D.modulusFP).add (BinaryFn.const 1)).bits_mem_FP,
    (F.encodedDegree_binary (determinantControls D).1 (determinantControls D).2
      (BinaryFn.fromBits D.innerFP) (BinaryFn.fromBits D.outerFP)).bits_mem_FP⟩

theorem valid_fppred {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    FPPred (fun c => Nat.fromBitsLE (inner c) < radix source D.bounds.degree c) :=
  (BinaryFn.fromBits D.innerFP).lt
    ((TubeBivariate.family source active modulus inner middle n d ell D.bounds).determinant.radix_binary
      (determinantControls D).1 (determinantControls D).2)

theorem familyEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) (outer : List Bool → List Bool) (ho : outer ∈ FP) :
    SpaceFunction (modularFamily source active modulus inner middle outer n d ell D.bounds).value := by
  have controls := originalControls D
  let F := modularFamily source active modulus inner middle outer n d ell D.bounds
  let a := originalAccess source active modulus inner middle n d ell D.bounds
  have hi : BinaryFn F.inner := BinaryFn.of_bits
    (mem_FP_of_eq controls.degree (originalAccess source active modulus inner middle n d ell D.bounds).degree_eq)
  exact F.evaluator a (determinantControls D).1 controls.modulus
    (BinaryFn.fromBits (entryDegreeCode_mem_FP D.sourceFP D.bounds.degreeFP)) hi
    (BinaryFn.fromBits ho) (originalEntryEvaluator D)


noncomputable def modularValue (source active modulus inner middle outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  IntegerBits.coefficientResidue (coefficient source active inner middle outer n d ell c) (Nat.fromBitsLE (modulus c) + 1)

attribute [local irreducible] coefficient

theorem evaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) (outer : List Bool → List Bool) (ho : outer ∈ FP) :
    SpaceFunction (modularValue source active modulus inner middle outer n d ell) := by
  have ES := familyEvaluator D outer ho
  have EB := SpaceFunction.branch (fun c => decide (Nat.fromBitsLE (inner c) < radix source D.bounds.degree c))
    (valid_fppred D).flag_mem_FP
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
