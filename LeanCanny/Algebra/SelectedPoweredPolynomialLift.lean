/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.SelectedParameterPolynomialLift
public import LeanCanny.Algebra.CoordinatePowerSubstitution
/-! # Selected determinant coefficients on the actual weighted joint tuple

Only evaluation of the representative is multiplicative. Its raw-variable
powers are the existing prefix weights and are not serialized into a new
spatial source or charged against the immutable source degree.
-/
@[expose] public section
namespace LeanCanny.Algebra.SelectedPoweredPolynomialLift
open Polynomial PrincipalSubresultant
open scoped Classical
variable {A K : Type*} [CommRing A] [CommRing K] {m N : ℕ}

noncomputable def representative (basis : IntegralCoordinateBasis A m N) (weights : Fin m→ℕ) (a : A) :=
  CoordinatePowerSubstitution.substitute weights (basis.representative a)

theorem evaluate (basis : IntegralCoordinateBasis A m N) (weights : Fin m→ℕ) (z : Fin m→K)
    (φ : A→ₐ[ℤ]K) (hφ : ∀ i,φ (basis.generator i)=z i^weights i) (a : A) :
    (MvPolynomial.aeval z) (representative basis weights a)=φ a := by
  have HE:=CoordinatePowerSubstitution.eval_substitute (Int.castRingHom K) weights (basis.representative a) z
  have HA:=basis.representative_eval_algHom a φ
  change (representative basis weights a).eval₂ (Int.castRingHom K) z=φ a
  rw [representative,HE]
  simpa only [MvPolynomial.aeval_def,algebraMap_int_eq,hφ] using HA

theorem principal (basis : IntegralCoordinateBasis A m N) (weights : Fin m→ℕ) (z : Fin m→K)
    (φ : A→ₐ[ℤ]K) (hφ : ∀ i,φ (basis.generator i)=z i^weights i)
    (p f : Polynomial (Polynomial A)) (d e u v D s j : ℕ)
    (hd : (p.map (Polynomial.mapRingHom φ.toRingHom)).natDegree≤d)
    (hp : ∀ i≤d,((p.coeff i).map φ.toRingHom).natDegree≤e)
    (hu : (f.map (Polynomial.mapRingHom φ.toRingHom)).natDegree≤u)
    (hf : ∀ i≤u,((f.coeff i).map φ.toRingHom).natDegree≤v) :
    (signedPsc (SelectedParameterPolynomialLift.lift p (representative basis weights) d e)
      (PseudoRemainder.seed (SelectedParameterPolynomialLift.lift p (representative basis weights) d e)
        (SelectedParameterPolynomialLift.lift f (representative basis weights) u v) d D) d s j).map
        (MvPolynomial.aeval z).toRingHom=
      signedPsc (p.map (Polynomial.mapRingHom φ.toRingHom))
        (PseudoRemainder.seed (p.map (Polynomial.mapRingHom φ.toRingHom))
          (f.map (Polynomial.mapRingHom φ.toRingHom)) d D) d s j :=
  SelectedParameterPolynomialLift.principal p f (representative basis weights) d e u v D s j φ.toRingHom
    (MvPolynomial.aeval z).toRingHom (evaluate basis weights z φ hφ) hd hp hu hf

end LeanCanny.Algebra.SelectedPoweredPolynomialLift
