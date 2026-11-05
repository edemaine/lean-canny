/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MacaulayQuotientSpecialization
public import LeanCanny.Algebra.ScaledPolynomialQuotient
/-! # The normalized universal value is an unscaled padded characteristic quotient

Both matrices keep the native full fixed-width index set. The explicit
reduced-count factor compensates their different identity padding. The
divisor is monic even when its value at zero vanishes.
-/
@[expose] public section
namespace LeanCanny.Algebra.MacaulayPaddedPolynomialValue
open MvPolynomial Polynomial
open scoped Classical BigOperators
variable {n : ℕ} {R : Type*} [CommRing R]

def reduced (d : Fin (n + 1) → ℕ) : ℕ := ∑ i, ∏ j ∈ Finset.univ.erase i, d j
def dimension (W : ℕ) : ℕ := FixedWidthPolynomial.count (n + 1) W

noncomputable def divisor (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (d : Fin (n + 1) → ℕ) (W : ℕ) := (Macaulay.extraneousPadded p d W).charpoly
noncomputable def dividend (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (d : Fin (n + 1) → ℕ) (W : ℕ) := (Macaulay.matrix p d W).charpoly * (1 - Polynomial.X) ^ reduced d
noncomputable def quotient (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (d : Fin (n + 1) → ℕ) (W : ℕ) :=
  ScaledPolynomialQuotient.quotient (divisor p d W) (dividend p d W) (dimension (n := n) W) (reduced d)

theorem factorization (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : Macaulay.level d < 2 ^ W) :
    dividend p d W = divisor p d W * Macaulay.characteristicQuotient p d W := by
  have HC := Macaulay.card_active_eq_extraneous_add d hd W hW
  have HA := Finset.card_add_card_compl (Macaulay.activeIndices d W)
  have HE := Finset.card_add_card_compl (Macaulay.extraneousIndices d W)
  have HCount : (Macaulay.activeIndices d W)ᶜ.card + reduced d = (Macaulay.extraneousIndices d W)ᶜ.card := by
    unfold reduced
    omega
  have HPad := PrincipalPadding.subtractive_determinant (Macaulay.matrix p d W) (Macaulay.extraneousIndices d W)
  change (AffineCharacteristic.subtractiveMatrix (Macaulay.extraneousPadded p d W)).det =
    (1 - Polynomial.X : Polynomial R) ^ (Macaulay.extraneousIndices d W)ᶜ.card *
      (AffineCharacteristic.subtractiveMatrix (Macaulay.extraneousMinor p d W)).det at HPad
  have HDet : Macaulay.characteristicNumerator p d W * (1 - Polynomial.X) ^ reduced d =
      (AffineCharacteristic.subtractiveMatrix (Macaulay.extraneousPadded p d W)).det *
        Macaulay.characteristicQuotient p d W := by
    rw [HPad, mul_assoc, ← Macaulay.characteristicQuotient_factorization p d W hp hd hW,
      Macaulay.characteristicNumerator_eq_padding_mul_active, ← HCount, pow_add]
    ring
  rw [Macaulay.characteristicNumerator, AffineCharacteristic.subtractive_det_eq_sign_mul_charpoly,
    AffineCharacteristic.subtractive_det_eq_sign_mul_charpoly] at HDet
  have HU : IsUnit (Polynomial.C ((-1 : R) ^ Fintype.card (Macaulay.Index (n + 1) W))) :=
    (isUnit_neg_one.pow _).map Polynomial.C
  apply HU.mul_left_cancel
  simpa only [dividend, divisor, mul_assoc] using HDet

section Domain
variable [IsDomain R]

theorem quotient_eq (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : Macaulay.level d < 2 ^ W) :
    quotient p d W = Macaulay.characteristicQuotient p d W := by
  have HD : (divisor p d W).natDegree = dimension (n := n) W := by
    simpa only [divisor, dimension, Fintype.card_fin] using Matrix.charpoly_natDegree_eq_dim (Macaulay.extraneousPadded p d W)
  have HL : (divisor p d W).coeff (dimension (n := n) W) = 1 := by
    have H := (Matrix.charpoly_monic (Macaulay.extraneousPadded p d W)).leadingCoeff
    change (divisor p d W).coeff (divisor p d W).natDegree = 1 at H
    exact (congrArg (divisor p d W).coeff HD).symm.trans H
  have HQ : (Macaulay.characteristicQuotient p d W).natDegree ≤ reduced d :=
    le_of_eq (Macaulay.characteristicQuotient_natDegree p d W hd hW)
  rw [quotient, factorization p d W hp hd hW,
    ScaledPolynomialQuotient.quotient_mul _ _ _ _ HD.le HQ, HL, one_pow, Polynomial.C_1, one_mul]

theorem value_eq_coefficient_zero (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) :
    MacaulayUniversal.polynomialValue d W hdegree hW p = (quotient p d W).coeff 0 := by
  rw [quotient_eq p d W hp hd hW, MacaulayUniversal.polynomialValue_eq_eval_zero d W hdegree hW p hp hd,
    ← Polynomial.coeff_zero_eq_eval_zero]

end Domain
end LeanCanny.Algebra.MacaulayPaddedPolynomialValue
