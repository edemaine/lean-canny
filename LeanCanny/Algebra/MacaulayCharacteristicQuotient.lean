/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CharacteristicPolynomialQuotient
public import LeanCanny.Algebra.MacaulayPolynomialCancellation
public import LeanCanny.Algebra.PolynomialQuotientLowest

/-! # The polynomial Macaulay characteristic quotient

The quotient is defined by monic polynomial division, independently of
homogeneity proofs. For homogeneous inputs of positive declared degrees
it factors the characteristic numerator exactly. Over a domain its degree
is the reduced-monomial count, its leading coefficient is the corresponding
dimension sign, and its lowest data agree with the prior rational quotient.
No multivariate-resultant root characterization is asserted here.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

noncomputable def characteristicQuotient (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) : Polynomial R :=
  AffineCharacteristic.quotientPolynomial (activeMinor p d W) (extraneousMinor p d W)

theorem characteristicQuotient_factorization (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : level d < 2 ^ W) :
    activeCharacteristic p d W = (AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det *
      characteristicQuotient p d W :=
  AffineCharacteristic.quotientPolynomial_factorization _ _
    (extraneous_characteristic_dvd_active_characteristic p d W hp hd hW)

theorem characteristicQuotient_map (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ) :
    (characteristicQuotient p d W).map φ = characteristicQuotient (fun i => (p i).map φ) d W := by
  rw [characteristicQuotient, characteristicQuotient, AffineCharacteristic.quotientPolynomial_map,
    activeMinor_map, extraneousMinor_map]

section Domain
variable [IsDomain R]

theorem characteristicQuotient_ne_zero (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : level d < 2 ^ W) :
    characteristicQuotient p d W ≠ 0 :=
  AffineCharacteristic.quotientPolynomial_ne_zero _ _
    (extraneous_characteristic_dvd_active_characteristic p d W hp hd hW)

theorem characteristicQuotient_natDegree (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hd : ∀ i, 0 < d i) (hW : level d < 2 ^ W) :
    (characteristicQuotient p d W).natDegree = ∑ i, ∏ j ∈ Finset.univ.erase i, d j := by
  rw [characteristicQuotient, AffineCharacteristic.quotientPolynomial_natDegree]
  simp only [Fintype.card_coe]
  have hc := card_active_eq_extraneous_add d hd W hW
  omega

theorem characteristicQuotient_leadingCoeff (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hd : ∀ i, 0 < d i) (hW : level d < 2 ^ W) :
    (characteristicQuotient p d W).leadingCoeff = (-1 : R) ^ (∑ i, ∏ j ∈ Finset.univ.erase i, d j) := by
  have hc : Fintype.card (extraneousIndices d W) ≤ Fintype.card (activeIndices d W) := by
    simp only [Fintype.card_coe]
    exact Finset.card_le_card (extraneousIndices_subset_active d W)
  rw [characteristicQuotient, AffineCharacteristic.quotientPolynomial_leadingCoeff _ _ hc]
  simp only [Fintype.card_coe]
  congr 1
  have he := card_active_eq_extraneous_add d hd W hW
  omega

theorem characteristicQuotient_signed_monic (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hd : ∀ i, 0 < d i) (hW : level d < 2 ^ W) :
    (Polynomial.C ((-1 : R) ^ (∑ i, ∏ j ∈ Finset.univ.erase i, d j)) * characteristicQuotient p d W).Monic := by
  change (Polynomial.C _ * characteristicQuotient p d W).leadingCoeff = 1
  rw [Polynomial.leadingCoeff_C_mul_of_isUnit (isUnit_neg_one.pow _), characteristicQuotient_leadingCoeff p d W hd hW]
  exact AffineCharacteristic.neg_one_pow_square _

theorem characteristicQuotient_natDegree_map [Nontrivial S] (φ : R →+* S)
    (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hd : ∀ i, 0 < d i) (hW : level d < 2 ^ W) :
    ((characteristicQuotient p d W).map φ).natDegree = ∑ i, ∏ j ∈ Finset.univ.erase i, d j := by
  rw [Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff φ (by
    rw [characteristicQuotient_leadingCoeff p d W hd hW]
    exact isUnit_neg_one.pow _)]
  exact characteristicQuotient_natDegree p d W hd hW

theorem characteristicQuotient_ratFunc (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : level d < 2 ^ W) :
    RatFunc.mk (activeCharacteristic p d W) (AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det =
      algebraMap (Polynomial R) (RatFunc R) (characteristicQuotient p d W) :=
  AffineCharacteristic.quotientPolynomial_ratFunc _ _
    (extraneous_characteristic_dvd_active_characteristic p d W hp hd hW)

theorem characteristicQuotient_lowest (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : level d < 2 ^ W) :
    PolynomialQuotientLowest.order (activeCharacteristic p d W)
        (AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det = (characteristicQuotient p d W).natTrailingDegree ∧
      PolynomialQuotientLowest.coefficient (activeCharacteristic p d W)
        (AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det =
          algebraMap R (FractionRing R) (characteristicQuotient p d W).trailingCoeff := by
  apply PolynomialQuotientLowest.of_polynomial
    (AffineCharacteristic.subtractive_det_ne_zero (extraneousMinor p d W)) (characteristicQuotient_ne_zero p d W hp hd hW)
  rw [characteristicQuotient_factorization p d W hp hd hW, mul_comm]

end Domain
end LeanCanny.Algebra.Macaulay
