/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SubresultantGCDGeneral
public import LeanCanny.Algebra.ScaledPolynomialQuotient
public import LeanCanny.Algebra.SquarefreePart
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Division-free squarefree preprocessing with a symbolic parameter

The coefficient ring is ℤ[alpha]. The first nonzero original principal
subresultant selects the GCD degree over its fraction field. The coefficient
form and a scaled Cramer quotient remain in ℤ[alpha][X]. No GCD, degree, or
separability oracle is an input to the construction.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicScaledSquarefree
open Polynomial PrincipalSubresultant
open scoped Classical
attribute [local irreducible] Matrix.det

abbrev Coefficient := Polynomial ℤ
abbrev CoefficientField := FractionRing Coefficient

noncomputable def embedding : Coefficient →+* CoefficientField := algebraMap _ _

theorem embedding_injective : Function.Injective embedding :=
  IsFractionRing.injective _ _

noncomputable def fractionPolynomial (p : Polynomial Coefficient) : Polynomial CoefficientField := p.map embedding

theorem fractionPolynomial_ne_zero {p : Polynomial Coefficient} (hp : p ≠ 0) :
    fractionPolynomial p ≠ 0 := (Polynomial.map_ne_zero_iff embedding_injective).mpr hp

theorem exists_nonzero_psc (p : Polynomial Coefficient) (hd : p.natDegree ≠ 0) :
    ∃ j, psc p p.derivative p.natDegree p.derivative.natDegree j ≠ 0 := by
  have hq : p.derivative ≠ 0 := derivative_ne_zero.mpr hd
  have hlt := natDegree_derivative_lt hd
  have h := (gcd_data (fractionPolynomial p) (fractionPolynomial p.derivative)
    (fractionPolynomial_ne_zero hq) (by
      simpa only [fractionPolynomial, natDegree_map_eq_of_injective embedding_injective] using hlt)).2.1
  refine ⟨(EuclideanDomain.gcd (fractionPolynomial p) (fractionPolynomial p.derivative)).natDegree, ?_⟩
  rw [fractionPolynomial, fractionPolynomial,
    natDegree_map_eq_of_injective embedding_injective,
    natDegree_map_eq_of_injective embedding_injective, psc_map_map] at h
  exact fun hz => h (by simpa only [fractionPolynomial, map_zero] using congrArg embedding hz)

noncomputable def degree (p : Polynomial Coefficient) : ℕ :=
  if hd : p.natDegree = 0 then 0 else Nat.find (exists_nonzero_psc p hd)

theorem degree_psc_ne_zero (p : Polynomial Coefficient) (hd : p.natDegree ≠ 0) :
    psc p p.derivative p.natDegree p.derivative.natDegree (degree p) ≠ 0 := by
  rw [degree, dite_eq_right hd]
  exact Nat.find_spec (exists_nonzero_psc p hd)

theorem psc_eq_zero_of_lt (p : Polynomial Coefficient) (hd : p.natDegree ≠ 0)
    (j : ℕ) (hj : j < degree p) :
    psc p p.derivative p.natDegree p.derivative.natDegree j = 0 := by
  rw [degree, dite_eq_right hd] at hj
  exact not_not.mp (Nat.find_min (exists_nonzero_psc p hd) hj)

theorem degree_eq_common (p : Polynomial Coefficient) :
    degree p = (SquarefreePart.common (fractionPolynomial p)).natDegree := by
  by_cases hd : p.natDegree = 0
  · have hp : (fractionPolynomial p).natDegree = 0 := by
      rw [fractionPolynomial, natDegree_map_eq_of_injective embedding_injective, hd]
    simp only [degree, hd, dite_true, SquarefreePart.common,
      derivative_eq_zero.mpr hp, EuclideanDomain.gcd_zero_right, hp]
  · have hdata := gcd_data (fractionPolynomial p) (fractionPolynomial p.derivative)
      (fractionPolynomial_ne_zero (derivative_ne_zero.mpr hd)) (by
        simpa only [fractionPolynomial, natDegree_map_eq_of_injective embedding_injective]
          using natDegree_derivative_lt hd)
    have he : fractionPolynomial p.derivative = (fractionPolynomial p).derivative := by
      simp only [fractionPolynomial, derivative_map]
    rw [he] at hdata
    have hnonzero : psc p p.derivative p.natDegree p.derivative.natDegree
        (SquarefreePart.common (fractionPolynomial p)).natDegree ≠ 0 := by
      intro hz
      apply hdata.2.1
      rw [← he, fractionPolynomial, fractionPolynomial,
        natDegree_map_eq_of_injective embedding_injective,
        natDegree_map_eq_of_injective embedding_injective, psc_map_map]
      simpa only [SquarefreePart.common, fractionPolynomial, derivative_map, map_zero] using congrArg embedding hz
    apply Nat.le_antisymm
    · rw [degree, dite_eq_right hd]
      exact Nat.find_min' (exists_nonzero_psc p hd) hnonzero
    · by_contra h
      have hj : degree p < (SquarefreePart.common (fractionPolynomial p)).natDegree := by omega
      have hz := hdata.2.2 (degree p) hj
      rw [← he, fractionPolynomial, fractionPolynomial,
        natDegree_map_eq_of_injective embedding_injective,
        natDegree_map_eq_of_injective embedding_injective, psc_map_map] at hz
      exact degree_psc_ne_zero p hd ((map_eq_zero_iff embedding embedding_injective).mp hz)

noncomputable def gcd (p : Polynomial Coefficient) : Polynomial Coefficient :=
  if p.natDegree = 0 then 1 else coefficientForm p p.derivative p.natDegree p.derivative.natDegree (degree p)

noncomputable def polynomial (p : Polynomial Coefficient) : Polynomial Coefficient :=
  ScaledPolynomialQuotient.quotient (gcd p) p (degree p) (p.natDegree - degree p)

theorem gcd_associated (p : Polynomial Coefficient) (hp : p ≠ 0) :
    Associated ((gcd p).map embedding) (SquarefreePart.common (fractionPolynomial p)) := by
  by_cases hd : p.natDegree = 0
  · have hP : (fractionPolynomial p).natDegree = 0 := by
      rw [fractionPolynomial, natDegree_map_eq_of_injective embedding_injective, hd]
    rw [gcd, ite_eq_left hd, Polynomial.map_one, SquarefreePart.common,
      derivative_eq_zero.mpr hP, EuclideanDomain.gcd_zero_right]
    apply Associated.symm
    apply associated_one_iff_isUnit.mpr
    rw [Polynomial.isUnit_iff_degree_eq_zero,
      degree_eq_natDegree (fractionPolynomial_ne_zero hp), hP]
    rfl
  · have h := (gcd_data (fractionPolynomial p) ((fractionPolynomial p).derivative)
      (derivative_ne_zero.mpr (by
        rw [fractionPolynomial, natDegree_map_eq_of_injective embedding_injective]
        exact hd)) (natDegree_derivative_lt (by
          rw [fractionPolynomial, natDegree_map_eq_of_injective embedding_injective]
          exact hd))).1
    rw [gcd, ite_eq_right hd, coefficientForm_map, degree_eq_common]
    simpa only [SquarefreePart.common, fractionPolynomial, derivative_map,
      natDegree_map_eq_of_injective embedding_injective] using h

theorem gcd_natDegree (p : Polynomial Coefficient) (hp : p ≠ 0) :
    (gcd p).natDegree = degree p := by
  have h := PrincipalSubresultant.natDegree_eq_of_associated (gcd_associated p hp)
  simpa only [natDegree_map_eq_of_injective embedding_injective, degree_eq_common] using h

theorem map_associated_part (p : Polynomial Coefficient) (hp : p ≠ 0) :
    Associated ((polynomial p).map embedding) (SquarefreePart.part (fractionPolynomial p)) := by
  let P := fractionPolynomial p
  let G := (gcd p).map embedding
  have hP : P ≠ 0 := fractionPolynomial_ne_zero hp
  have ha : Associated G (SquarefreePart.common P) := gcd_associated p hp
  have hg : G ≠ 0 := ha.ne_zero_iff.mpr (SquarefreePart.common_ne_zero P hP)
  have hdiv : G ∣ P := ha.dvd.trans (EuclideanDomain.gcd_dvd_left P P.derivative)
  have hfact : G * (P / G) = P := EuclideanDomain.mul_div_cancel' hg hdiv
  have hh : P / G ≠ 0 := by intro hz; rw [hz, mul_zero] at hfact; exact hP hfact.symm
  have hd : G.natDegree = degree p := by
    dsimp only [G]
    rw [natDegree_map_eq_of_injective embedding_injective, gcd_natDegree p hp]
  have hquot : (P / G).natDegree ≤ p.natDegree - degree p := by
    have h := natDegree_mul hg hh
    rw [hfact, hd] at h
    have he : P.natDegree = p.natDegree := natDegree_map_eq_of_injective embedding_injective p
    omega
  have hqassoc : Associated (P / G) (SquarefreePart.part P) :=
    Associated.of_mul_left (Associated.of_eq (hfact.trans (SquarefreePart.factorization P hP).symm)) ha hg
  have hmap : (polynomial p).map embedding = C (G.coeff (degree p) ^ (p.natDegree - degree p + 1)) * (P / G) := by
    rw [polynomial, ScaledPolynomialQuotient.quotient_map]
    change ScaledPolynomialQuotient.quotient G P _ _ = _
    have h := ScaledPolynomialQuotient.quotient_mul G (P / G) (degree p) (p.natDegree - degree p) hd.le hquot
    rw [hfact] at h
    exact h
  have hlc : G.coeff (degree p) ≠ 0 := by
    rw [← hd, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hg
  rw [hmap]
  exact (associated_unit_mul_left (P / G) _
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hlc)))).trans hqassoc

theorem separable (p : Polynomial Coefficient) (hp : p ≠ 0) :
    ((polynomial p).map embedding).Separable :=
  (map_associated_part p hp).symm.separable
    (SquarefreePart.separable _ (fractionPolynomial_ne_zero hp))

theorem polynomial_ne_zero (p : Polynomial Coefficient) (hp : p ≠ 0) : polynomial p ≠ 0 := by
  apply (Polynomial.map_ne_zero_iff embedding_injective).mp
  exact (map_associated_part p hp).ne_zero_iff.mpr
    (SquarefreePart.part_ne_zero _ (fractionPolynomial_ne_zero hp))

theorem polynomial_natDegree_le (p : Polynomial Coefficient) :
    (polynomial p).natDegree ≤ p.natDegree :=
  (ScaledPolynomialQuotient.quotient_degree _ _ _ _).trans (Nat.sub_le _ _)

private theorem eval₂_zero_of_dvd {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : S) {p q : R[X]} (h : p ∣ q) (hp : p.eval₂ f a = 0) : q.eval₂ f a = 0 := by
  obtain ⟨r, rfl⟩ := h
  rw [eval₂_mul, hp, zero_mul]

theorem roots_iff {L : Type*} [Field L] [CharZero L]
    (f : CoefficientField →+* L) (p : Polynomial Coefficient) (hp : p ≠ 0) (a : L) :
    (polynomial p).eval₂ (f.comp embedding) a = 0 ↔ p.eval₂ (f.comp embedding) a = 0 := by
  have ha := map_associated_part p hp
  have hroot : ((polynomial p).map embedding).eval₂ f a = 0 ↔
      (SquarefreePart.part (fractionPolynomial p)).eval₂ f a = 0 :=
    ⟨eval₂_zero_of_dvd _ _ ha.dvd, eval₂_zero_of_dvd _ _ ha.dvd'⟩
  have h := hroot.trans (SquarefreePart.eval₂_eq_zero_iff f _ (fractionPolynomial_ne_zero hp) a)
  simpa only [fractionPolynomial, Polynomial.eval₂_map] using h

end LeanCanny.Algebra.SymbolicScaledSquarefree
