/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CharacteristicLowestBounds
public import LeanCanny.Algebra.CharacteristicPolynomialQuotient

/-! # Lowest numerator bounds with a retained sweep parameter

Swapping the two entry parameters bounds the inner degree of every
characteristic coefficient. Kronecker encoding then transfers the integer
determinant coefficient budget back without constructing a dense polynomial.
-/

@[expose] public section

namespace LeanCanny.Algebra.CharacteristicLowestBounds
open Polynomial
open scoped BigOperators Classical

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

theorem map_coefficient {S : Type*} [CommRing S] (φ : Polynomial R →+* Polynomial S)
    (A : Matrix ι ι (Polynomial R)) (k : ℕ) :
    φ ((AffineCharacteristic.subtractiveMatrix A).det.coeff k) =
      (AffineCharacteristic.subtractiveMatrix (A.map φ)).det.coeff k := by
  rw [← Polynomial.coeff_map, AffineCharacteristic.subtractive_det_map]

theorem coefficient_inner_degree_le (A : Matrix ι ι (Polynomial (Polynomial R))) (E : ℕ)
    (hA : ∀ r s j, ((A r s).coeff j).natDegree ≤ E) (k j : ℕ) :
    (((AffineCharacteristic.subtractiveMatrix A).det.coeff k).coeff j).natDegree ≤ Fintype.card ι * E := by
  let φ : Polynomial (Polynomial R) →+* Polynomial (Polynomial R) := Polynomial.Bivariate.swap.toRingHom
  have hdeg : ∀ r s, ((A.map φ) r s).natDegree ≤ E := by
    intro r s
    exact (PolynomialKronecker.inner_degree_iff_swap (A r s) E).mp (hA r s)
  have hd := coefficient_degree_le (A.map φ) E hdeg k
  rw [← map_coefficient φ A k] at hd
  exact (PolynomialKronecker.inner_degree_iff_swap _ _).mpr hd j

theorem lowest_inner_degree_le (A : Matrix ι ι (Polynomial (Polynomial R))) (E : ℕ)
    (hA : ∀ r s j, ((A r s).coeff j).natDegree ≤ E) (j : ℕ) :
    ((lowest A).coeff j).natDegree ≤ Fintype.card ι * E := coefficient_inner_degree_le A E hA _ j

omit [CommRing R] [Fintype ι] [DecidableEq ι] in
theorem encode_mass_le (B : ℕ) (p : Polynomial (Polynomial ℤ)) :
    coefficientMass (PolynomialKronecker.encode B p) ≤ NestedMass.mass p := by
  rw [PolynomialKronecker.encode_sum, NestedMass.range_sum p (p.natDegree + 1) (by omega)]
  apply (coefficientMass_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  have h := coefficientMass_mul_le (p.coeff j) (Polynomial.X ^ (B * j))
  simpa only [Polynomial.X_pow_eq_monomial, coefficientMass_monomial, Int.natAbs_one, mul_one] using h

omit [CommRing R] in
theorem bivariate_coefficient_size_le (A : Matrix ι ι (Polynomial (Polynomial ℤ))) (E b : ℕ)
    (hdeg : ∀ r s j, ((A r s).coeff j).natDegree ≤ E)
    (hmass : ∀ r s, NestedMass.mass (A r s) ≤ 2 ^ b) (k j i : ℕ) :
    ((((AffineCharacteristic.subtractiveMatrix A).det.coeff k).coeff j).coeff i).natAbs.size ≤
      (Fintype.card ι).size * Fintype.card ι + Fintype.card ι * (b + 1) + 1 := by
  let B := Fintype.card ι * E + 1
  let G := (AffineCharacteristic.subtractiveMatrix A).det.coeff k
  have hG (l : ℕ) : (G.coeff l).natDegree < B :=
    (coefficient_inner_degree_le A E hdeg k l).trans_lt (Nat.lt_succ_self _)
  by_cases hi : i < B
  · have hc := PolynomialKronecker.coefficient B G hG i j hi
    rw [map_coefficient (PolynomialKronecker.encode B) A k] at hc
    rw [← hc]
    apply all_coefficient_size_le (A.map (PolynomialKronecker.encode B)) b
    intro r s
    exact (encode_mass_le B (A r s)).trans (hmass r s)
  · have hz : (G.coeff j).coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt ((hG j).trans_le (by omega))
    change ((G.coeff j).coeff i).natAbs.size ≤ _
    rw [hz]
    simp

omit [CommRing R] in
theorem lowest_bivariate_coefficient_size_le (A : Matrix ι ι (Polynomial (Polynomial ℤ))) (E b : ℕ)
    (hdeg : ∀ r s j, ((A r s).coeff j).natDegree ≤ E)
    (hmass : ∀ r s, NestedMass.mass (A r s) ≤ 2 ^ b) (j i : ℕ) :
    (((lowest A).coeff j).coeff i).natAbs.size ≤
      (Fintype.card ι).size * Fintype.card ι + Fintype.card ι * (b + 1) + 1 :=
  bivariate_coefficient_size_le A E b hdeg hmass _ j i

end LeanCanny.Algebra.CharacteristicLowestBounds
