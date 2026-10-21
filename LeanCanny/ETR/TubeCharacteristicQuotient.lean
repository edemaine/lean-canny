/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationCharacteristicSpace
public import LeanCanny.ETR.TubeExtraneousCharacteristicSpace
public import LeanCanny.Algebra.MacaulaySubtractiveSystem
public import LeanCanny.Algebra.PolynomialQuotientLowest

/-! # The actual tube characteristic determinant quotient

The numerator uses the true degree-level Macaulay matrix; the denominator
uses the true extraneous principal minor. Both are nonzero, and their lowest
data agree with the certified padded computations. The quotient is defined as
a rational function. `TubeCharacteristicPolynomial` constructs its polynomial
representative; identification with the multivariate resultant remains open.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open LeanCanny.Encoding LeanCanny.Algebra

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

noncomputable def numerator (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : Polynomial (Polynomial (Polynomial ℤ)) :=
  Macaulay.activeCharacteristic (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))

theorem numerator_padding (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    TubeDeformation.characteristicPolynomial source active n d ell c =
      (1 - Polynomial.X : Polynomial (Polynomial (Polynomial ℤ))) ^
        (Macaulay.activeIndices (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c)))ᶜ.card *
          numerator source active n d ell c :=
  Macaulay.characteristicNumerator_eq_padding_mul_active _ _ _

theorem numerator_lowest (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    (numerator source active n d ell c).natTrailingDegree =
      (TubeDeformation.characteristicPolynomial source active n d ell c).natTrailingDegree ∧
    (numerator source active n d ell c).trailingCoeff =
      (TubeDeformation.characteristicPolynomial source active n d ell c).trailingCoeff :=
  let h := Macaulay.characteristicNumerator_lowest_active (TubeBivariate.rows source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
  ⟨h.1.symm, h.2.symm⟩

theorem numerator_ne_zero (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : numerator source active n d ell c ≠ 0 := by
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mp
  rw [(numerator_lowest source active n d ell c).2]
  exact TubeDeformation.characteristicLowest_ne_zero source active n d ell c

theorem denominator_ne_zero (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    TubeExtraneous.characteristicPolynomial source active n d ell c ≠ 0 :=
  Polynomial.trailingCoeff_nonzero_iff_nonzero.mp (TubeExtraneous.characteristicLowest_ne_zero source active n d ell c)

theorem numerator_shifted (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    numerator source active n d ell c =
      (Macaulay.activeMinor (Macaulay.subtractiveSystem (TubeBivariate.rows source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c))
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))).det := by
  exact (congrArg Matrix.det (Macaulay.activeMinor_subtractiveSystem
    (TubeBivariate.rows source active n d ell c) (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (TubeCleared.matrixWidth (source c)))).symm

theorem denominator_shifted (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    TubeExtraneous.characteristicPolynomial source active n d ell c =
      (Macaulay.extraneousMinor (Macaulay.subtractiveSystem (TubeBivariate.rows source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c))
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))).det := by
  exact (congrArg Matrix.det (Macaulay.extraneousMinor_subtractiveSystem
    (TubeBivariate.rows source active n d ell c) (MacaulayBits.Degrees (TubeCleared.layout source) c)
    (TubeCleared.matrixWidth (source c)))).symm

noncomputable def value (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : RatFunc (Polynomial (Polynomial ℤ)) :=
  PolynomialQuotientLowest.quotient (numerator source active n d ell c) (TubeExtraneous.characteristicPolynomial source active n d ell c)

theorem value_ne_zero (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : value source active n d ell c ≠ 0 := by
  rw [value, PolynomialQuotientLowest.quotient, RatFunc.mk_eq_div]
  exact div_ne_zero (RatFunc.algebraMap_ne_zero (numerator_ne_zero source active n d ell c))
    (RatFunc.algebraMap_ne_zero (denominator_ne_zero source active n d ell c))

theorem value_eq_shifted_determinants (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    value source active n d ell c = RatFunc.mk
      (Macaulay.activeMinor (Macaulay.subtractiveSystem (TubeBivariate.rows source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c))
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))).det
      (Macaulay.extraneousMinor (Macaulay.subtractiveSystem (TubeBivariate.rows source active n d ell c)
        (MacaulayBits.Degrees (TubeCleared.layout source) c))
        (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))).det := by
  rw [value, PolynomialQuotientLowest.quotient, numerator_shifted, denominator_shifted]

noncomputable def order (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : ℤ :=
  PolynomialQuotientLowest.order (numerator source active n d ell c) (TubeExtraneous.characteristicPolynomial source active n d ell c)

noncomputable def lowestCoefficient (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : FractionRing (Polynomial (Polynomial ℤ)) :=
  PolynomialQuotientLowest.coefficient (numerator source active n d ell c) (TubeExtraneous.characteristicPolynomial source active n d ell c)

theorem lowestCoefficient_eq (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    lowestCoefficient source active n d ell c =
      algebraMap (Polynomial (Polynomial ℤ)) (FractionRing (Polynomial (Polynomial ℤ)))
          (TubeDeformation.characteristicPolynomial source active n d ell c).trailingCoeff /
        algebraMap (Polynomial (Polynomial ℤ)) (FractionRing (Polynomial (Polynomial ℤ)))
          (TubeExtraneous.characteristicPolynomial source active n d ell c).trailingCoeff := by
  rw [lowestCoefficient, PolynomialQuotientLowest.coefficient, (numerator_lowest source active n d ell c).2]

noncomputable def numeratorScalar (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : ℤ :=
  (((numerator source active n d ell c).trailingCoeff).coeff (Nat.fromBitsLE (middle c))).coeff (Nat.fromBitsLE (inner c))

theorem numeratorScalar_eq (source active inner middle : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    numeratorScalar source active inner middle n d ell c = TubeDeformation.characteristicScalar source active inner middle n d ell c := by
  rw [numeratorScalar, (numerator_lowest source active n d ell c).2]
  rfl

theorem order_eq (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    order source active n d ell c =
      (Nat.fromBitsLE (TubeDeformation.lowestIndex source active n d ell c) : ℤ) -
        Nat.fromBitsLE (TubeExtraneous.lowestIndex source active n d ell c) := by
  rw [order, PolynomialQuotientLowest.order, (numerator_lowest source active n d ell c).1,
    (TubeDeformation.characteristicPolynomial_lowest source active n d ell c).1,
    (TubeExtraneous.characteristicPolynomial_lowest source active n d ell c).1, TubeExtraneous.lowestIndex_value]

theorem of_polynomial (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)
    (p : Polynomial (Polynomial (Polynomial ℤ)))
    (h : numerator source active n d ell c = p * TubeExtraneous.characteristicPolynomial source active n d ell c) :
    order source active n d ell c = p.natTrailingDegree ∧
      lowestCoefficient source active n d ell c = algebraMap _ _ p.trailingCoeff := by
  have hp : p ≠ 0 := by
    intro hz
    exact numerator_ne_zero source active n d ell c (by rw [h, hz, zero_mul])
  exact PolynomialQuotientLowest.of_polynomial (denominator_ne_zero source active n d ell c) hp h

theorem lowestData_of_representation (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)
    (p q : Polynomial (Polynomial (Polynomial ℤ))) (hp : p ≠ 0) (hq : q ≠ 0)
    (h : PolynomialQuotientLowest.quotient p q = value source active n d ell c) :
    PolynomialQuotientLowest.order p q = order source active n d ell c ∧
      PolynomialQuotientLowest.coefficient p q = lowestCoefficient source active n d ell c :=
  PolynomialQuotientLowest.invariant hp hq (numerator_ne_zero source active n d ell c)
    (denominator_ne_zero source active n d ell c) h

end LeanCanny.ETR.TubeCharacteristicQuotient
