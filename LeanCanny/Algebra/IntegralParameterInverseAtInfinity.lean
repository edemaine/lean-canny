/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralParameterInverseSpecialization
public import LeanCanny.Algebra.IntegerPolynomialOuterSign
/-! # A proved outer cutoff for the actual inverse constructor's selected index

An actual integer parameter-polynomial presentation with bounded coefficient
mass supplies every coefficient-survival guard. Above the common cutoff,
degree, trailing index, denominator and inverse all specialize exactly.
Constructing that presentation for a recursive interpreter remains separate.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralParameterInverseAtInfinity
open Polynomial

noncomputable def parameterEval (x :ℝ) :ℤ[X]→+*ℝ:=
  Polynomial.eval₂RingHom (Int.castRingHom ℝ) x

theorem nonzero_after_mass (q :ℤ[X]) (hq :q≠0) (b :ℕ)
    (hb :coefficientMass q≤2^b) (x :ℝ) (hx :(2:ℝ)^(b+1)≤x):
    parameterEval x q≠0:=by
  have HS:=IntegerPolynomialOuterSign.sign_after_binary_mass q b hb x hx
  have HL :(q.leadingCoeff:ℝ)≠0:=Int.cast_ne_zero.mpr (leadingCoeff_ne_zero.mpr hq)
  intro HZ
  change q.eval₂ (Int.castRingHom ℝ) x=0 at HZ
  have HE :SignType.sign (q.leadingCoeff:ℝ)=0:=by
    simpa only [HZ,sign_zero] using HS.symm
  exact HL (sign_eq_zero_iff.mp HE)

theorem coefficient_ne_zero_iff (p :(ℤ[X])[X]) (b :ℕ)
    (hb :∀k,coefficientMass (p.coeff k)≤2^b) (x :ℝ) (hx :(2:ℝ)^(b+1)≤x) (k :ℕ):
    parameterEval x (p.coeff k)≠0 ↔p.coeff k≠0:=by
  constructor
  · intro H HZ
    exact H (by rw [HZ,map_zero])
  · exact fun H=>nonzero_after_mass _ H b (hb k) x hx

theorem natDegree_after_mass (p :(ℤ[X])[X]) (b :ℕ)
    (hb :∀k,coefficientMass (p.coeff k)≤2^b) (x :ℝ) (hx :(2:ℝ)^(b+1)≤x):
    (p.map (parameterEval x)).natDegree=p.natDegree:=by
  by_cases hp :p=0
  · subst p
    simp
  · apply natDegree_map_of_leadingCoeff_ne_zero
    exact (coefficient_ne_zero_iff p b hb x hx p.natDegree).mpr (leadingCoeff_ne_zero.mpr hp)

theorem natTrailingDegree_after_mass (p :(ℤ[X])[X]) (b :ℕ)
    (hb :∀k,coefficientMass (p.coeff k)≤2^b) (x :ℝ) (hx :(2:ℝ)^(b+1)≤x):
    (p.map (parameterEval x)).natTrailingDegree=p.natTrailingDegree:=by
  by_cases hp :p=0
  · subst p
    simp
  · apply IntegralParameterInverse.natTrailingDegree_map_at
    · intro k hk
      rw [coeff_eq_zero_of_lt_natTrailingDegree hk,map_zero]
    · exact (coefficient_ne_zero_iff p b hb x hx p.natTrailingDegree).mpr
        (Polynomial.trailingCoeff_ne_zero.mpr hp)

theorem denominator_after_mass (p :(ℤ[X])[X]) (b :ℕ)
    (hb :∀k,coefficientMass (p.coeff k)≤2^b) (x :ℝ) (hx :(2:ℝ)^(b+1)≤x):
    IntegralParameterInverse.denominator (p.map (parameterEval x))=
      parameterEval x (IntegralParameterInverse.denominator p):=by
  simp only [IntegralParameterInverse.denominator,trailingCoeff,
    natTrailingDegree_after_mass p b hb x hx,coeff_map]

theorem inverse_after_mass (p :(ℤ[X])[X]) (b :ℕ)
    (hb :∀k,coefficientMass (p.coeff k)≤2^b) (x :ℝ) (hx :(2:ℝ)^(b+1)≤x):
    IntegralParameterInverse.inverse (p.map (parameterEval x))=
      (IntegralParameterInverse.inverse p).map (parameterEval x):=by
  ext k
  simp only [IntegralParameterInverse.coeff_inverse,coeff_map,map_neg,
    natTrailingDegree_after_mass p b hb x hx]

end LeanCanny.Algebra.IntegralParameterInverseAtInfinity
