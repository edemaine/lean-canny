/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.BoundedRegularRadiusExponents

/-! # One external radius parameter for the actual integer regular sources

The parameter is the physical radius `2^R`. Spatial polynomials remain the
coefficient ring; this construction does not change their initial spatial
degree or compile the parameter into a new spatial source.
-/
@[expose] public section
namespace LeanCanny.Geometry.BoundedRegularRadius
open LeanCanny.Algebra
open scoped BigOperators Classical

noncomputable def powerScalar {ι : Type*} (offset slope : ℕ) : Polynomial (MvPolynomial ι ℤ) :=
  Polynomial.C (MvPolynomial.C ((2 : ℤ)^offset))*Polynomial.X^slope

theorem powerScalar_eval {ι : Type*} (offset slope R : ℕ) :
    (powerScalar (ι:=ι) offset slope).eval (MvPolynomial.C ((2 : ℤ)^R))=
      MvPolynomial.C ((2 : ℤ)^(offset+slope*R)) := by
  calc
    _=MvPolynomial.C ((2 : ℤ)^offset*((2 : ℤ)^R)^slope) := by
      simp only [powerScalar,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,map_mul,map_pow]
    _=MvPolynomial.C ((2 : ℤ)^(offset+slope*R)) := by
      rw [←pow_mul,←pow_add,Nat.mul_comm R slope]

noncomputable def sourcePolynomial {n : ℕ} (q : MvPolynomial (Fin n) ℤ) :
    Polynomial (MvPolynomial (Fin (n+4)) ℤ) :=
  Polynomial.C (MvPolynomial.rename (Fin.castAdd 2) (MvPolynomial.rename (Fin.castAdd 2) q))^2+
    (Polynomial.C (∑ j : Fin (n+2),MvPolynomial.X (Fin.castAdd 2 j)^2)-Polynomial.X^2)^2

theorem sourcePolynomial_eval {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (R : ℕ) :
    (sourcePolynomial q).eval (MvPolynomial.C ((2 : ℤ)^R))=
      MvPolynomial.rename (Fin.castAdd 2) (BoundedZeroSource.polynomial q R) := by
  have HR : BoundedZeroSource.radiusSquared R=((2 : ℤ)^R)^2 := by
    unfold BoundedZeroSource.radiusSquared
    rw [←pow_mul,Nat.mul_comm R 2]
  simp only [sourcePolynomial,Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_sub,
    Polynomial.eval_X,BoundedZeroSource.polynomial,BoundedZeroSource.sphere,
    map_add,map_pow,map_sub,map_sum,Polynomial.eval_finsetSum,MvPolynomial.rename_C,MvPolynomial.rename_X,HR]

noncomputable def polynomial {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b : ℕ) :
    Polynomial (MvPolynomial (Fin (n+4)) ℤ) :=
  powerScalar (BoundedRegularSource.regularizationExponent n D b 0) (regularizationSlope n D)*
    (powerScalar (BoundedZeroSource.perturbationExponent n D b 0) (perturbationSlope n D)*sourcePolynomial q-
      powerScalar (BoundedZeroSource.penaltyExponent n D 0) (BoundedZeroSource.powerDegree D)+
      Polynomial.C (∑ j : Fin (n+4),MvPolynomial.X j^BoundedZeroSource.powerDegree D))-1

theorem polynomial_eval {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) :
    (polynomial q D b).eval (MvPolynomial.C ((2 : ℤ)^R))=BoundedRegularSource.polynomial q D b R := by
  simp only [polynomial,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_one,powerScalar_eval,sourcePolynomial_eval]
  rw [←regularization_affine n D b R,←perturbation_affine n D b R,←penalty_affine n D R]
  unfold BoundedRegularSource.polynomial
  rw [IntegerRegularSource.polynomial_eq]
  simp only [BoundedRegularSource.lower,FermatCriticalHomogenization.polynomial,MvPolynomial.C_1,one_mul,
    IntegerRegularSource.scale]
  rfl

end LeanCanny.Geometry.BoundedRegularRadius
