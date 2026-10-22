/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicScaledSquarefreeBounds
public import LeanCanny.Algebra.EffectiveInfinitesimalSign

/-! # Ordinary specialization of symbolic squarefree preprocessing

Evaluation of alpha need not be injective. Nonvanishing of the actual leading
coefficient and selected principal subresultant suffices to preserve the GCD
order and the roots of the scaled quotient.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicScaledSquarefree
open Polynomial PrincipalSubresultant
open scoped Classical
attribute [local irreducible] Matrix.det

variable {L : Type*} [Field L] [CharZero L]

theorem specialized_gcd_data (φ : Coefficient →+* L) (p : Polynomial Coefficient)
    (hlc : φ p.leadingCoeff ≠ 0)
    (hpsc : p.natDegree ≠ 0 → φ (psc p p.derivative p.natDegree p.derivative.natDegree (degree p)) ≠ 0) :
    Associated ((gcd p).map φ) (SquarefreePart.common (p.map φ)) ∧
      (SquarefreePart.common (p.map φ)).natDegree = degree p := by
  have hm : (p.map φ).natDegree = p.natDegree := natDegree_map_eq_iff.mpr (Or.inl hlc)
  have hn : p.map φ ≠ 0 := by
    intro hz
    have h := congrArg (fun q : L[X] => q.coeff p.natDegree) hz
    rw [coeff_map, coeff_natDegree, coeff_zero] at h
    exact hlc h
  by_cases hd : p.natDegree = 0
  · have hzero : (p.map φ).natDegree = 0 := hm.trans hd
    have hcommon : SquarefreePart.common (p.map φ) = p.map φ := by
      rw [SquarefreePart.common, derivative_eq_zero.mpr hzero, EuclideanDomain.gcd_zero_right]
    rw [gcd, ite_eq_left hd, Polynomial.map_one, hcommon]
    constructor
    · apply Associated.symm
      apply associated_one_iff_isUnit.mpr
      rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree hn, hzero]
      rfl
    · simp only [degree, hd, dite_true, hzero]
  · have hdm : (p.derivative.map φ).natDegree = p.derivative.natDegree := by
      rw [← derivative_map, natDegree_derivative, natDegree_derivative, hm]
    have hdn : p.derivative.map φ ≠ 0 := by
      rw [← derivative_map]
      apply derivative_ne_zero.mpr
      rwa [hm]
    have hdata := gcd_data (p.map φ) (p.derivative.map φ) hdn (by
      rw [hdm, hm]
      exact natDegree_derivative_lt hd)
    let k := (EuclideanDomain.gcd (p.map φ) (p.derivative.map φ)).natDegree
    have hk : k = degree p := by
      apply Nat.le_antisymm
      · by_contra h
        have hz := hdata.2.2 (degree p) (by dsimp [k] at *; omega)
        rw [hm, hdm, psc_map_map] at hz
        exact hpsc hd hz
      · by_contra h
        have hz := psc_eq_zero_of_lt p hd k (by omega)
        have hz' := hdata.2.1
        rw [hm, hdm, psc_map_map] at hz'
        exact hz' (by simpa only [k, map_zero] using congrArg φ hz)
    constructor
    · rw [gcd, ite_eq_right hd, coefficientForm_map]
      have ha := hdata.1
      rw [hm, hdm, show (EuclideanDomain.gcd (p.map φ) (p.derivative.map φ)).natDegree = degree p from hk] at ha
      simpa only [SquarefreePart.common, derivative_map] using ha
    · simpa only [SquarefreePart.common, derivative_map, k] using hk

theorem specialized_associated_part (φ : Coefficient →+* L) (p : Polynomial Coefficient)
    (hlc : φ p.leadingCoeff ≠ 0)
    (hpsc : p.natDegree ≠ 0 → φ (psc p p.derivative p.natDegree p.derivative.natDegree (degree p)) ≠ 0) :
    Associated ((polynomial p).map φ) (SquarefreePart.part (p.map φ)) := by
  let P := p.map φ
  let G := (gcd p).map φ
  have hP : P ≠ 0 := by
    intro hz
    have h := congrArg (fun q : L[X] => q.coeff p.natDegree) hz
    rw [coeff_map, coeff_natDegree, coeff_zero] at h
    exact hlc h
  obtain ⟨ha, hdcommon⟩ := specialized_gcd_data φ p hlc hpsc
  have hg : G ≠ 0 := ha.ne_zero_iff.mpr (SquarefreePart.common_ne_zero P hP)
  have hdiv : G ∣ P := ha.dvd.trans (EuclideanDomain.gcd_dvd_left P P.derivative)
  have hfact : G * (P / G) = P := EuclideanDomain.mul_div_cancel' hg hdiv
  have hh : P / G ≠ 0 := by intro hz; rw [hz, mul_zero] at hfact; exact hP hfact.symm
  have hd : G.natDegree = degree p :=
    (PrincipalSubresultant.natDegree_eq_of_associated ha).trans hdcommon
  have hquot : (P / G).natDegree ≤ p.natDegree - degree p := by
    have h := natDegree_mul hg hh
    rw [hfact, hd] at h
    have hm : P.natDegree = p.natDegree := natDegree_map_eq_iff.mpr (Or.inl hlc)
    omega
  have hqassoc : Associated (P / G) (SquarefreePart.part P) :=
    Associated.of_mul_left (Associated.of_eq (hfact.trans (SquarefreePart.factorization P hP).symm)) ha hg
  have hmap : (polynomial p).map φ = C (G.coeff (degree p) ^ (p.natDegree - degree p + 1)) * (P / G) := by
    rw [polynomial, ScaledPolynomialQuotient.quotient_map]
    change ScaledPolynomialQuotient.quotient G P _ _ = _
    have h := ScaledPolynomialQuotient.quotient_mul G (P / G) (degree p) (p.natDegree - degree p) hd.le hquot
    rw [hfact] at h
    exact h
  have hlcG : G.coeff (degree p) ≠ 0 := by
    rw [← hd, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hg
  rw [hmap]
  exact (associated_unit_mul_left (P / G) _
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hlcG)))).trans hqassoc

theorem specialized_separable (φ : Coefficient →+* L) (p : Polynomial Coefficient)
    (hlc : φ p.leadingCoeff ≠ 0)
    (hpsc : p.natDegree ≠ 0 → φ (psc p p.derivative p.natDegree p.derivative.natDegree (degree p)) ≠ 0) :
    ((polynomial p).map φ).Separable := by
  apply (specialized_associated_part φ p hlc hpsc).symm.separable
  apply SquarefreePart.separable
  intro hz
  have h := congrArg (fun q : L[X] => q.coeff p.natDegree) hz
  exact hlc (by simpa only [coeff_map, coeff_natDegree, coeff_zero] using h)

theorem specialized_roots_iff (φ : Coefficient →+* L) (p : Polynomial Coefficient)
    (hlc : φ p.leadingCoeff ≠ 0)
    (hpsc : p.natDegree ≠ 0 → φ (psc p p.derivative p.natDegree p.derivative.natDegree (degree p)) ≠ 0)
    (a : L) : (polynomial p).eval₂ φ a = 0 ↔ p.eval₂ φ a = 0 := by
  have ha := specialized_associated_part φ p hlc hpsc
  have hh : p.map φ ≠ 0 := by
    intro hz
    have h := congrArg (fun q : L[X] => q.coeff p.natDegree) hz
    exact hlc (by simpa only [coeff_map, coeff_natDegree, coeff_zero] using h)
  have hr : ((polynomial p).map φ).eval a = 0 ↔ (SquarefreePart.part (p.map φ)).eval a = 0 := by
    constructor
    · intro h
      obtain ⟨r, he⟩ := ha.dvd
      rw [he, eval_mul, h, zero_mul]
    · intro h
      obtain ⟨r, he⟩ := ha.dvd'
      rw [he, eval_mul, h, zero_mul]
  simpa only [Polynomial.eval_map, Polynomial.IsRoot] using
    hr.trans (SquarefreePart.roots_iff (p.map φ) hh a)

end LeanCanny.Algebra.SymbolicScaledSquarefree
