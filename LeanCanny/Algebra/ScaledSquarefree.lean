/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialGCDData
public import LeanCanny.Algebra.ScaledPolynomialQuotient
public import LeanCanny.Algebra.SquarefreePart

/-! # An integer square-free polynomial from determinantal GCD and division

The GCD and scaled quotient use only integer determinants. The output is
associated over the rationals to the canonical square-free part, so it is
separable and preserves roots in every characteristic-zero field.
-/

@[expose] public section

namespace LeanCanny.Algebra.ScaledSquarefree
open Polynomial
open scoped Classical

noncomputable def gcd (p : ℤ[X]) : ℤ[X] := PolynomialGCDBits.representative p p.derivative
noncomputable def degree (p : ℤ[X]) : ℕ := PolynomialGCDBits.degree p p.derivative
noncomputable def polynomial (p : ℤ[X]) : ℤ[X] :=
  ScaledPolynomialQuotient.quotient (gcd p) p (degree p) (p.natDegree - degree p)

theorem gcd_constant (p : ℤ[X]) (hz : p.natDegree = 0) : gcd p = 1 := by
  have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hd : p.derivative = 0 := derivative_eq_zero.mpr hz
  have he : PolynomialGCDBits.degree p p.derivative = 0 := by
    simp only [PolynomialGCDBits.degree, hd, Polynomial.map_zero, EuclideanDomain.gcd_zero_right,
      natDegree_map_eq_of_injective hi, hz]
  rw [gcd, PolynomialGCDBits.representative, he, hd, hz, natDegree_zero]
  simp [PrincipalSubresultant.coefficientForm]

theorem gcd_associated (p : ℤ[X]) (hp : p ≠ 0) :
    Associated ((gcd p).map (Int.castRingHom ℚ)) (SquarefreePart.common (p.map (Int.castRingHom ℚ))) := by
  have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hp' : p.map (Int.castRingHom ℚ) ≠ 0 := (Polynomial.map_ne_zero_iff hi).mpr hp
  by_cases hz : p.natDegree = 0
  · have hd : (p.map (Int.castRingHom ℚ)).derivative = 0 := derivative_eq_zero.mpr (by
      rw [natDegree_map_eq_of_injective hi, hz])
    rw [gcd_constant p hz, Polynomial.map_one, SquarefreePart.common, hd, EuclideanDomain.gcd_zero_right]
    apply Associated.symm
    apply associated_one_iff_isUnit.mpr
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree hp', natDegree_map_eq_of_injective hi, hz]
    rfl
  · simpa only [gcd, SquarefreePart.common, derivative_map] using
      PolynomialGCDBits.representative_associated p p.derivative (derivative_ne_zero.mpr hz) (natDegree_derivative_lt hz)

theorem gcd_natDegree (p : ℤ[X]) : (gcd p).natDegree = degree p := by
  by_cases hz : p.natDegree = 0
  · rw [gcd_constant p hz, natDegree_one]
    have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
    simp only [degree, PolynomialGCDBits.degree, derivative_eq_zero.mpr hz, Polynomial.map_zero,
      EuclideanDomain.gcd_zero_right, natDegree_map_eq_of_injective hi, hz]
  · exact PolynomialGCDBits.representative_natDegree p p.derivative (derivative_ne_zero.mpr hz) (natDegree_derivative_lt hz)

theorem map_associated_part (p : ℤ[X]) (hp : p ≠ 0) :
    Associated ((polynomial p).map (Int.castRingHom ℚ)) (SquarefreePart.part (p.map (Int.castRingHom ℚ))) := by
  let P := p.map (Int.castRingHom ℚ)
  let G := (gcd p).map (Int.castRingHom ℚ)
  have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hp' : P ≠ 0 := (Polynomial.map_ne_zero_iff hi).mpr hp
  have ha : Associated G (SquarefreePart.common P) := gcd_associated p hp
  have hg : G ≠ 0 := ha.ne_zero_iff.mpr (SquarefreePart.common_ne_zero P hp')
  have hdiv : G ∣ P := ha.dvd.trans (EuclideanDomain.gcd_dvd_left P P.derivative)
  have hfact : G * (P / G) = P := EuclideanDomain.mul_div_cancel' hg hdiv
  have hh : P / G ≠ 0 := by intro hz; rw [hz, mul_zero] at hfact; exact hp' hfact.symm
  have hd : G.natDegree = degree p := by
    dsimp only [G]
    rw [natDegree_map_eq_of_injective hi, gcd_natDegree]
  have hhdegree : (P / G).natDegree ≤ p.natDegree - degree p := by
    have h := natDegree_mul hg hh
    rw [hfact, hd] at h
    have hP : P.natDegree = p.natDegree := natDegree_map_eq_of_injective hi p
    omega
  have hqassoc : Associated (P / G) (SquarefreePart.part P) :=
    Associated.of_mul_left (Associated.of_eq (hfact.trans (SquarefreePart.factorization P hp').symm)) ha hg
  have hmap : (polynomial p).map (Int.castRingHom ℚ) =
      C (G.coeff (degree p) ^ (p.natDegree - degree p + 1)) * (P / G) := by
    rw [polynomial, ScaledPolynomialQuotient.quotient_map]
    change ScaledPolynomialQuotient.quotient G P _ _ = _
    have h := ScaledPolynomialQuotient.quotient_mul G (P / G) (degree p) (p.natDegree - degree p) hd.le hhdegree
    rw [hfact] at h
    exact h
  have hlc : G.coeff (degree p) ≠ 0 := by
    rw [← hd, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hg
  rw [hmap]
  exact (associated_unit_mul_left (P / G) _ (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hlc)))).trans hqassoc

theorem separable (p : ℤ[X]) (hp : p ≠ 0) : ((polynomial p).map (Int.castRingHom ℚ)).Separable :=
  (map_associated_part p hp).symm.separable (SquarefreePart.separable _
    ((Polynomial.map_ne_zero_iff (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)).mpr hp))

theorem separable_in_field {L : Type*} [Field L] [CharZero L] (p : ℤ[X]) (hp : p ≠ 0) :
    ((polynomial p).map (Int.castRingHom L)).Separable := by
  have h := (Polynomial.separable_map (Rat.castHom L)).mpr (separable p hp)
  have hc : (Rat.castHom L).comp (Int.castRingHom ℚ) = Int.castRingHom L := by ext z; simp
  simpa only [Polynomial.map_map, hc] using h

theorem polynomial_ne_zero (p : ℤ[X]) (hp : p ≠ 0) : polynomial p ≠ 0 := by
  have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have h := (map_associated_part p hp).ne_zero_iff.mpr
    (SquarefreePart.part_ne_zero _ ((Polynomial.map_ne_zero_iff hi).mpr hp))
  exact (Polynomial.map_ne_zero_iff hi).mp h

theorem polynomial_natDegree (p : ℤ[X]) (hp : p ≠ 0) :
    (polynomial p).natDegree = (SquarefreePart.part (p.map (Int.castRingHom ℚ))).natDegree := by
  have hi : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have h := PrincipalSubresultant.natDegree_eq_of_associated (map_associated_part p hp)
  simpa only [natDegree_map_eq_of_injective hi] using h

private theorem eval₂_zero_of_dvd {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : S) {p q : R[X]} (h : p ∣ q) (hp : p.eval₂ f a = 0) : q.eval₂ f a = 0 := by
  obtain ⟨r, rfl⟩ := h
  rw [eval₂_mul, hp, zero_mul]

theorem roots_iff {L : Type*} [Field L] [CharZero L] (p : ℤ[X]) (hp : p ≠ 0) (a : L) :
    (polynomial p).eval₂ (Int.castRingHom L) a = 0 ↔ p.eval₂ (Int.castRingHom L) a = 0 := by
  have ha := map_associated_part p hp
  have hroot : ((polynomial p).map (Int.castRingHom ℚ)).eval₂ (Rat.castHom L) a = 0 ↔
      (SquarefreePart.part (p.map (Int.castRingHom ℚ))).eval₂ (Rat.castHom L) a = 0 :=
    ⟨eval₂_zero_of_dvd _ _ ha.dvd, eval₂_zero_of_dvd _ _ ha.dvd'⟩
  have h := hroot.trans (SquarefreePart.eval₂_eq_zero_iff (Rat.castHom L) _
    ((Polynomial.map_ne_zero_iff (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)).mpr hp) a)
  have hc : (Rat.castHom L).comp (Int.castRingHom ℚ) = Int.castRingHom L := by ext z; simp
  simpa only [Polynomial.eval₂_map, hc] using h

end LeanCanny.Algebra.ScaledSquarefree
