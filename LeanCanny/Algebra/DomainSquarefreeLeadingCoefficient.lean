/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.DomainSquarefree
public import LeanCanny.Algebra.ScaledPolynomialQuotientTopCoefficient
/-! # The actual domain squarefree polynomial's leading coefficient

Only the original leading coefficient and the selected principal coefficient
are needed; no full quotient or coefficient-form expansion is required.
-/
@[expose] public section
namespace LeanCanny.Algebra.DomainSquarefree
open Polynomial PrincipalSubresultant
open scoped Classical
variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
set_option backward.isDefEq.respectTransparency false

theorem leading_coefficient (p : Polynomial R) (hp : p.natDegree ≠ 0) :
    (polynomial p).leadingCoeff = p.leadingCoeff *
      psc p p.derivative p.natDegree (p.natDegree - 1) (index p) ^ (p.natDegree - index p) := by
  let D := p.natDegree
  let k := index p
  let L := D - k
  let G := coefficientForm p p.derivative D (D - 1) k
  let Q := ScaledPolynomialQuotient.quotient G p k L
  have HV := valid_fraction p hp
  have HK : k < D := HV.index_lt
  have HG : G.natDegree ≤ k := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    rw [show G = coefficientForm p p.derivative D (D - 1) k from rfl,
      coefficientForm_coeff, ite_eq_right (by omega)]
  have HC : G.coeff k = psc p p.derivative D (D - 1) k := by
    rw [show G = coefficientForm p p.derivative D (D - 1) k from rfl,
      coefficientForm_coeff, ite_eq_left le_rfl, subresultantCoeff_self]
  have HS : psc p p.derivative D (D - 1) k ≠ 0 := by
    intro HZ
    exact HV.selected (by rw [HZ, map_zero])
  have HN : p ≠ 0 := by
    intro HZ
    exact hp (by rw [HZ, Polynomial.natDegree_zero])
  have HD : p.coeff D ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr HN
  have HT : Q.coeff L = psc p p.derivative D (D - 1) k ^ L * p.coeff D := by
    rw [show Q = ScaledPolynomialQuotient.quotient G p k L from rfl,
      ScaledPolynomialQuotient.top_coefficient G p k L HG, HC,
      show k + L = D by dsimp only [L]; omega]
  have HTop : Q.coeff L ≠ 0 := by rw [HT]; exact mul_ne_zero (pow_ne_zero _ HS) HD
  have HQ : Q.natDegree = L := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (ScaledPolynomialQuotient.quotient_degree G p k L) HTop
  have HE : polynomial p = Q := by
    rw [polynomial, ite_eq_right hp]
    rfl
  rw [HE, Polynomial.leadingCoeff, HQ, HT]
  exact mul_comm _ _

end LeanCanny.Algebra.DomainSquarefree
