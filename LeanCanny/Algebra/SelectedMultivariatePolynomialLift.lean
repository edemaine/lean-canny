/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SelectedPoweredPolynomialLift
public import Mathlib.Algebra.MvPolynomial.Equiv
/-! # Integer multivariate representatives for selected parameter tests

The first variable is the parameter and the remaining variables are the
same weighted raw joint tuple. Its coefficients are precisely the original
coefficient representatives, with finite degree guards. A determinant over
this ring specializes to the selected old hom, not an absolute norm.
-/
@[expose] public section
namespace LeanCanny.Algebra.SelectedMultivariatePolynomialLift
open Polynomial PrincipalSubresultant
open scoped Classical
variable {A C : Type*} [CommRing A] [CommRing C] {m : ℕ}

noncomputable def lift (p : Polynomial (Polynomial A)) (representative : A→MvPolynomial (Fin m) ℤ) (d e : ℕ) :
    Polynomial (MvPolynomial (Fin (m+1)) ℤ) :=
  (SelectedParameterPolynomialLift.lift p representative d e).map (MvPolynomial.finSuccEquiv ℤ m).symm.toRingHom

noncomputable def evaluate (φ : MvPolynomial (Fin m) ℤ→+*C) : MvPolynomial (Fin (m+1)) ℤ→+*Polynomial C :=
  (Polynomial.mapRingHom φ).comp (MvPolynomial.finSuccEquiv ℤ m).toRingHom

theorem coefficient (p : Polynomial (Polynomial A)) (representative : A→MvPolynomial (Fin m) ℤ) (d e y k : ℕ)
    (v : Fin m→₀ℕ) :
    ((lift p representative d e).coeff y).coeff (v.cons k)=
      if y≤d then if k≤e then (representative ((p.coeff y).coeff k)).coeff v else 0 else 0 := by
  rw [lift,Polynomial.coeff_map,←MvPolynomial.finSuccEquiv_coeff_coeff]
  change (((MvPolynomial.finSuccEquiv ℤ m) ((MvPolynomial.finSuccEquiv ℤ m).symm
    ((SelectedParameterPolynomialLift.lift p representative d e).coeff y))).coeff k).coeff v=_
  rw [AlgEquiv.apply_symm_apply]
  change (((SelectedPolynomialLift.lift p (fun q=>SelectedPolynomialLift.lift q representative e) d).coeff y).coeff k).coeff v=_
  rw [SelectedPolynomialLift.coefficient]
  by_cases hy : y≤d
  · rw [ite_eq_left hy,SelectedPolynomialLift.coefficient]
    by_cases hk : k≤e
    · rw [ite_eq_left hk,ite_eq_left hy,ite_eq_left hk]
    · rw [ite_eq_right hk,ite_eq_left hy,ite_eq_right hk]
      rfl
  · rw [ite_eq_right hy,ite_eq_right hy]
    rfl

theorem map_lift (p : Polynomial (Polynomial A)) (representative : A→MvPolynomial (Fin m) ℤ) (d e : ℕ)
    (select : A→+*C) (φ : MvPolynomial (Fin m) ℤ→+*C) (he : ∀ a,φ (representative a)=select a)
    (hd : (p.map (Polynomial.mapRingHom select)).natDegree≤d)
    (hp : ∀ i≤d,((p.coeff i).map select).natDegree≤e) :
    (lift p representative d e).map (evaluate φ)=p.map (Polynomial.mapRingHom select) := by
  rw [lift,Polynomial.map_map]
  have HC : (evaluate φ).comp (MvPolynomial.finSuccEquiv ℤ m).symm.toRingHom=Polynomial.mapRingHom φ := by
    apply RingHom.ext
    intro q
    change (Polynomial.mapRingHom φ) ((MvPolynomial.finSuccEquiv ℤ m) ((MvPolynomial.finSuccEquiv ℤ m).symm q))=_
    rw [AlgEquiv.apply_symm_apply]
  rw [HC]
  exact SelectedParameterPolynomialLift.map_lift p representative d e select φ he hd hp

end LeanCanny.Algebra.SelectedMultivariatePolynomialLift
