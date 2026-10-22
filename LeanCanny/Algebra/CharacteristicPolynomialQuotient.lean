/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CharacteristicQuotientDegree
public import Mathlib.Algebra.Polynomial.Div

/-! # Canonical polynomial quotients of characteristic determinants

Division by the denominator matrix's monic characteristic polynomial,
with its dimension sign, defines a polynomial over the original ring.
When the subtractive determinants divide, this polynomial is their exact
quotient. The construction commutes with all coefficient maps.
-/

@[expose] public section

namespace LeanCanny.Algebra.AffineCharacteristic
open scoped Classical Matrix
variable {R S I J : Type*} [CommRing R] [CommRing S] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem subtractive_det_eq_sign_mul_charpoly (A : Matrix I I R) :
    (subtractiveMatrix A).det = Polynomial.C ((-1 : R) ^ Fintype.card I) * A.charpoly := by
  rw [subtractive_det_eq_charpoly]
  simp only [map_pow, map_neg, map_one]

noncomputable def quotientPolynomial (A : Matrix I I R) (E : Matrix J J R) : Polynomial R :=
  Polynomial.C ((-1 : R) ^ Fintype.card J) * ((subtractiveMatrix A).det /ₘ E.charpoly)

theorem neg_one_pow_square (m : ℕ) : (-1 : R) ^ m * (-1 : R) ^ m = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

theorem quotientPolynomial_eq_of_factorization (A : Matrix I I R) (E : Matrix J J R) (q : Polynomial R)
    (hq : (subtractiveMatrix A).det = (subtractiveMatrix E).det * q) : quotientPolynomial A E = q := by
  have hd : (subtractiveMatrix A).det /ₘ E.charpoly = Polynomial.C ((-1 : R) ^ Fintype.card J) * q := by
    rw [hq, subtractive_det_eq_sign_mul_charpoly]
    have hm : (Polynomial.C ((-1 : R) ^ Fintype.card J) * E.charpoly) * q =
        E.charpoly * (Polynomial.C ((-1 : R) ^ Fintype.card J) * q) := by ring
    rw [hm, Polynomial.mul_divByMonic_cancel_left _ E.charpoly_monic]
  rw [quotientPolynomial, hd, ← mul_assoc, ← map_mul, neg_one_pow_square, map_one, one_mul]

theorem quotientPolynomial_factorization (A : Matrix I I R) (E : Matrix J J R)
    (hdiv : (subtractiveMatrix E).det ∣ (subtractiveMatrix A).det) :
    (subtractiveMatrix A).det = (subtractiveMatrix E).det * quotientPolynomial A E := by
  obtain ⟨q, hq⟩ := hdiv
  rw [quotientPolynomial_eq_of_factorization A E q hq]
  exact hq

theorem subtractive_det_map (φ : R →+* S) (A : Matrix I I R) :
    ((subtractiveMatrix A).det).map φ = (subtractiveMatrix (A.map φ)).det := by
  rw [subtractive_det_eq_sign_mul_charpoly, subtractive_det_eq_sign_mul_charpoly,
    Polynomial.map_mul, Polynomial.map_C, map_pow, map_neg, map_one, Matrix.charpoly_map]

theorem quotientPolynomial_map (φ : R →+* S) (A : Matrix I I R) (E : Matrix J J R) :
    (quotientPolynomial A E).map φ = quotientPolynomial (A.map φ) (E.map φ) := by
  rw [quotientPolynomial, quotientPolynomial, Polynomial.map_mul, Polynomial.map_C, map_pow, map_neg, map_one,
    Polynomial.map_divByMonic φ E.charpoly_monic, subtractive_det_map, Matrix.charpoly_map]

section Domain
variable [IsDomain R]

theorem quotientPolynomial_ne_zero (A : Matrix I I R) (E : Matrix J J R)
    (hdiv : (subtractiveMatrix E).det ∣ (subtractiveMatrix A).det) : quotientPolynomial A E ≠ 0 := by
  intro hz
  have he := quotientPolynomial_factorization A E hdiv
  rw [hz, mul_zero] at he
  exact subtractive_det_ne_zero A he

theorem quotientPolynomial_natDegree (A : Matrix I I R) (E : Matrix J J R) :
    (quotientPolynomial A E).natDegree = Fintype.card I - Fintype.card J := by
  rw [quotientPolynomial, Polynomial.natDegree_C_mul_of_isUnit (isUnit_neg_one.pow _),
    Polynomial.natDegree_divByMonic _ E.charpoly_monic, subtractive_det_natDegree, Matrix.charpoly_natDegree_eq_dim]

theorem quotientPolynomial_leadingCoeff (A : Matrix I I R) (E : Matrix J J R)
    (hc : Fintype.card J ≤ Fintype.card I) :
    (quotientPolynomial A E).leadingCoeff = (-1 : R) ^ (Fintype.card I - Fintype.card J) := by
  have hdegree : E.charpoly.degree ≤ (subtractiveMatrix A).det.degree := by
    rw [Polynomial.degree_eq_natDegree E.charpoly_monic.ne_zero,
      Polynomial.degree_eq_natDegree (subtractive_det_ne_zero A), Matrix.charpoly_natDegree_eq_dim, subtractive_det_natDegree]
    exact_mod_cast hc
  rw [quotientPolynomial, Polynomial.leadingCoeff_C_mul_of_isUnit (isUnit_neg_one.pow _),
    Polynomial.leadingCoeff_divByMonic_of_monic E.charpoly_monic hdegree, subtractive_det_eq_sign_mul_charpoly,
    Polynomial.leadingCoeff_C_mul_of_isUnit (isUnit_neg_one.pow _), A.charpoly_monic.leadingCoeff, mul_one, ← pow_add]
  calc
    _ = (-1 : R) ^ ((Fintype.card J + Fintype.card J) + (Fintype.card I - Fintype.card J)) := by
      congr 1
      omega
    _ = _ := by rw [pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem quotientPolynomial_unique (A : Matrix I I R) (E : Matrix J J R)
    (hdiv : (subtractiveMatrix E).det ∣ (subtractiveMatrix A).det) (q : Polynomial R)
    (hq : (subtractiveMatrix A).det = (subtractiveMatrix E).det * q) : q = quotientPolynomial A E := by
  apply mul_left_cancel₀ (subtractive_det_ne_zero E)
  exact hq.symm.trans (quotientPolynomial_factorization A E hdiv)

theorem quotientPolynomial_ratFunc (A : Matrix I I R) (E : Matrix J J R)
    (hdiv : (subtractiveMatrix E).det ∣ (subtractiveMatrix A).det) :
    RatFunc.mk (subtractiveMatrix A).det (subtractiveMatrix E).det =
      algebraMap (Polynomial R) (RatFunc R) (quotientPolynomial A E) := by
  rw [RatFunc.mk_eq_div, quotientPolynomial_factorization A E hdiv, map_mul]
  exact mul_div_cancel_left₀ _ (RatFunc.algebraMap_ne_zero (subtractive_det_ne_zero E))

end Domain
end LeanCanny.Algebra.AffineCharacteristic
