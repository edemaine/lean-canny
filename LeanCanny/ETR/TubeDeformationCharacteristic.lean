/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationLowestLanguages
public import LeanCanny.Algebra.MacaulayCharacteristic

/-! # Characteristic numerator of the actual full tube matrix

The subtractive determinant det(A-sI) is the ordinary characteristic polynomial
times the padded dimension sign. Its lowest coefficient is the computed affine
lowest coefficient times the lowest-order sign. Every coefficient specialization
therefore has the same zero condition. The resultant quotient is not identified.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
open Complexity LeanCanny.Encoding LeanCanny.Algebra

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det determinant lowestCoefficient lowestScalar

noncomputable def characteristicPolynomial (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : Polynomial (Polynomial (Polynomial ℤ)) :=
  Macaulay.characteristicNumerator (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))

theorem characteristicPolynomial_eq_charpoly (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    characteristicPolynomial source active n d ell c =
      (-1 : Polynomial (Polynomial (Polynomial ℤ))) ^
        FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) *
          (TubeBivariate.integerMatrix source active n d ell c).charpoly :=
  Macaulay.characteristicNumerator_eq_charpoly _ _ _

theorem characteristicPolynomial_lowest (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    (characteristicPolynomial source active n d ell c).natTrailingDegree =
      Nat.fromBitsLE (lowestIndex source active n d ell c) ∧
    (characteristicPolynomial source active n d ell c).trailingCoeff =
      (-1 : Polynomial (Polynomial ℤ)) ^ Nat.fromBitsLE (lowestIndex source active n d ell c) *
        lowestCoefficient source active n d ell c := by
  rw [lowestIndex_value]
  unfold characteristicPolynomial lowestCoefficient determinant matrix system
  exact Macaulay.characteristicNumerator_lowest (R := Polynomial (Polynomial ℤ))
    (TubeBivariate.rows source active n d ell c) (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))

theorem characteristicLowest_eval_zero_iff {K : Type*} [CommRing K]
    (φ : Polynomial (Polynomial ℤ) →+* K) (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    φ (characteristicPolynomial source active n d ell c).trailingCoeff = 0 ↔
      φ (lowestCoefficient source active n d ell c) = 0 := by
  rw [(characteristicPolynomial_lowest source active n d ell c).2, map_mul, map_pow, map_neg, map_one,
    PolynomialSignedReflection.sign_mul_eq_zero_iff]

theorem characteristicLowest_ne_zero (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    (characteristicPolynomial source active n d ell c).trailingCoeff ≠ 0 := by
  intro hz
  exact lowestCoefficient_ne_zero source active n d ell c
    ((characteristicLowest_eval_zero_iff (RingHom.id (Polynomial (Polynomial ℤ))) source active n d ell c).mp hz)

noncomputable def characteristicScalar (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : ℤ :=
  (((characteristicPolynomial source active n d ell c).trailingCoeff).coeff (Nat.fromBitsLE (middle c))).coeff (Nat.fromBitsLE (inner c))

theorem characteristicScalar_eq (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    characteristicScalar source active inner middle n d ell c =
      (-1 : ℤ) ^ Nat.fromBitsLE (lowestIndex source active n d ell c) * lowestScalar source active inner middle n d ell c := by
  rw [characteristicScalar, (characteristicPolynomial_lowest source active n d ell c).2]
  have hs : Polynomial.C (Polynomial.C ((-1 : ℤ) ^ Nat.fromBitsLE (lowestIndex source active n d ell c))) =
      (-1 : Polynomial (Polynomial ℤ)) ^ Nat.fromBitsLE (lowestIndex source active n d ell c) := by
    simp only [map_pow, map_neg, map_one]
  rw [← hs, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  unfold lowestScalar
  rfl

theorem characteristicScalar_zero_iff (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    characteristicScalar source active inner middle n d ell c = 0 ↔ lowestScalar source active inner middle n d ell c = 0 := by
  rw [characteristicScalar_eq, PolynomialSignedReflection.sign_mul_eq_zero_iff]

end LeanCanny.ETR.TubeDeformation
