/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeExtraneousLowestLanguages

/-! # Characteristic denominator of the actual extraneous principal minor

The subtractive characteristic determinant uses the true principal index set.
Its lowest coefficient agrees, up to the lowest-order sign, with the nonzero
identity-padded affine deformation. No resultant quotient formula is assumed.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeExtraneous
open Complexity LeanCanny.Encoding LeanCanny.Algebra

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det lowestCoefficient lowestScalar

noncomputable def principalMatrix (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :=
  Macaulay.extraneousMinor (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))

noncomputable def characteristicPolynomial (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : Polynomial (Polynomial (Polynomial ℤ)) :=
  (AffineCharacteristic.subtractiveMatrix (principalMatrix source active n d ell c)).det

theorem characteristicPolynomial_eq_charpoly (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    characteristicPolynomial source active n d ell c =
      (-1 : Polynomial (Polynomial (Polynomial ℤ))) ^ (indices source c).card *
        (principalMatrix source active n d ell c).charpoly := by
  have h := AffineCharacteristic.subtractive_det_eq_charpoly (R := Polynomial (Polynomial ℤ))
    (principalMatrix source active n d ell c)
  change (AffineCharacteristic.subtractiveMatrix (principalMatrix source active n d ell c)).det =
    (-1 : Polynomial (Polynomial (Polynomial ℤ))) ^
      Fintype.card (Macaulay.extraneousIndices (MacaulayBits.Degrees (TubeCleared.layout source) c)
        (TubeCleared.matrixWidth (source c))) * (principalMatrix source active n d ell c).charpoly at h
  rw [Fintype.card_coe] at h
  exact h

theorem characteristicPolynomial_lowest (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    (characteristicPolynomial source active n d ell c).natTrailingDegree =
      (determinant source active n d ell c).natTrailingDegree ∧
    (characteristicPolynomial source active n d ell c).trailingCoeff =
      (-1 : Polynomial (Polynomial ℤ)) ^ (determinant source active n d ell c).natTrailingDegree *
        (determinant source active n d ell c).trailingCoeff :=
  Macaulay.extraneous_characteristic_lowest (TubeBivariate.rows source active n d ell c) _ _

theorem characteristicLowest_eval_zero_iff {K : Type*} [CommRing K]
    (φ : Polynomial (Polynomial ℤ) →+* K) (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    φ (characteristicPolynomial source active n d ell c).trailingCoeff = 0 ↔
      φ (determinant source active n d ell c).trailingCoeff = 0 := by
  rw [(characteristicPolynomial_lowest source active n d ell c).2, map_mul, map_pow, map_neg, map_one,
    PolynomialSignedReflection.sign_mul_eq_zero_iff]

theorem characteristicLowest_ne_zero (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    (characteristicPolynomial source active n d ell c).trailingCoeff ≠ 0 := by
  intro hz
  have hd := (characteristicLowest_eval_zero_iff (RingHom.id (Polynomial (Polynomial ℤ))) source active n d ell c).mp hz
  exact determinant_ne_zero source active n d ell c (Polynomial.trailingCoeff_eq_zero.mp hd)

noncomputable def characteristicScalar (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : ℤ :=
  (((characteristicPolynomial source active n d ell c).trailingCoeff).coeff (Nat.fromBitsLE (middle c))).coeff (Nat.fromBitsLE (inner c))

theorem characteristicScalar_eq (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    characteristicScalar source active inner middle n d ell c =
      (-1 : ℤ) ^ Nat.fromBitsLE (lowestIndex source active n d ell c) * lowestScalar source active inner middle n d ell c := by
  rw [characteristicScalar, (characteristicPolynomial_lowest source active n d ell c).2, ← lowestIndex_value]
  have hs : Polynomial.C (Polynomial.C ((-1 : ℤ) ^ Nat.fromBitsLE (lowestIndex source active n d ell c))) =
      (-1 : Polynomial (Polynomial ℤ)) ^ Nat.fromBitsLE (lowestIndex source active n d ell c) := by
    simp only [map_pow, map_neg, map_one]
  rw [← hs, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  unfold lowestScalar lowestCoefficient
  rfl

theorem characteristicScalar_zero_iff (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    characteristicScalar source active inner middle n d ell c = 0 ↔ lowestScalar source active inner middle n d ell c = 0 := by
  rw [characteristicScalar_eq, PolynomialSignedReflection.sign_mul_eq_zero_iff]

end LeanCanny.ETR.TubeExtraneous
