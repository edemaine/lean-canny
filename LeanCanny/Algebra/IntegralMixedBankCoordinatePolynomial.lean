/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRetainedRealBound
public import LeanCanny.Algebra.ScaledGradedReductionAnnihilator
public import LeanCanny.Geometry.IntegralMixedCanonicalBankPoint
/-! # Integer annihilators of actual retained bank quotients

A common-cleared multiplication matrix has eigenvalue Q times the retained
coordinate. Substituting Q*X in its characteristic polynomial annihilates the
coordinate itself, independently of a later sampler's width or horizon.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedBankCoordinatePolynomial
open IntegralMixedHistory Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def matrix (x : State P S B m ι) (i : Fin m) :=
  Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (cleared x i)

noncomputable def polynomial (x : State P S B m ι) (i : Fin m) : Polynomial ℤ :=
  ScaledGradedReductionAnnihilator.polynomial (matrix x i) (commonDenominator x) 1

theorem coefficient (x : State P S B m ι) (i : Fin m) (k : ℕ) :
    (polynomial x i).coeff k=(matrix x i).charpoly.coeff k*commonDenominator x^k := by
  rw [polynomial,ScaledGradedReductionAnnihilator.coefficient,Nat.one_mul]

theorem degree (x : State P S B m ι) (i : Fin m) :
    (polynomial x i).natDegree=FixedWidthPolynomial.count m B := by
  rw [polynomial,ScaledGradedReductionAnnihilator.polynomial,pow_one,Polynomial.natDegree_comp,
    Matrix.charpoly_natDegree_eq_dim,Polynomial.natDegree_C_mul_X _ (commonDenominator_ne_zero x),Nat.mul_one]
  exact Fintype.card_fin _

theorem leading (x : State P S B m ι) (i : Fin m) :
    (polynomial x i).leadingCoeff=commonDenominator x^FixedWidthPolynomial.count m B := by
  have HD : (Polynomial.C (commonDenominator x)*Polynomial.X).natDegree≠0 := by
    rw [Polynomial.natDegree_C_mul_X _ (commonDenominator_ne_zero x)]
    decide
  rw [polynomial,ScaledGradedReductionAnnihilator.polynomial,pow_one,Polynomial.leadingCoeff_comp HD,
    (Matrix.charpoly_monic (matrix x i)).leadingCoeff,one_mul,
    Polynomial.leadingCoeff_C_mul_X,Matrix.charpoly_natDegree_eq_dim]
  rw [Fintype.card_fin]

theorem nonzero (x : State P S B m ι) (i : Fin m) : polynomial x i≠0 := by
  intro h
  have H := congrArg Polynomial.leadingCoeff h
  rw [leading,Polynomial.leadingCoeff_zero] at H
  exact pow_ne_zero _ (commonDenominator_ne_zero x) H

theorem quotient_root (x : State P S B m ι) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (i : Fin m) :
    (polynomial x i).eval₂ (Int.castRingHom ℝ) (φ (x.bank.numerator i)/(x.bank.denominator i:ℝ))=0 := by
  have HQ : (commonDenominator x:ℝ)≠0 := Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)
  have HR := CommonIntegerDenominator.recover φ.toRingHom Finset.univ x.bank.denominator x.bank.numerator
    (fun j _ => x.denominator_ne_zero j) i (Finset.mem_univ _)
  have HE : (commonDenominator x:ℝ)*(φ (x.bank.numerator i)/(x.bank.denominator i:ℝ))=φ (cleared x i) :=
    (mul_comm _ _).trans ((div_eq_iff HQ).mp HR).symm
  apply ScaledGradedReductionAnnihilator.root (matrix x i) (commonDenominator x) 1 (Int.castRingHom ℝ)
  change (matrix x i).charpoly.eval₂ (Int.castRingHom ℝ)
    ((commonDenominator x:ℝ)^1*(φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)))=0
  rw [pow_one,HE]
  exact IntegralParameterInverse.charpoly_root x.sampler.scalarPrefix.basis.finBasis (cleared x i) φ

theorem point_root (x : State P S B m ι) (H : Canonical x) (z : Fin m→ℝ)
    (hz : ∀ i,(x.sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom ℝ) z=0) (i : Fin m) :
    (polynomial x i).eval₂ (Int.castRingHom ℝ) (LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point x z i)=0 := by
  obtain ⟨φ,_,hvalues⟩ := LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.interprets x H z hz
  rw [←hvalues i]
  exact quotient_root x φ i

end LeanCanny.Algebra.IntegralMixedBankCoordinatePolynomial
