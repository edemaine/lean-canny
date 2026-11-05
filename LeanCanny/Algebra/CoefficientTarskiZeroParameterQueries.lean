/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthBivariateZeroLift
/-! # Literal eta-zero lift over an arbitrary coefficient base

Only the source parameter is killed. Epsilon remains an independent axis.
-/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientTarskiZeroParameterQueries
open Polynomial
open scoped Classical
variable {R S : Type*} [CommRing R] [CommRing S] {m : ℕ}

noncomputable def zeroHom (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin (m+1)) R →+* MvPolynomial (Fin m) R :=
  (Polynomial.constantCoeff : Polynomial (MvPolynomial (Fin m) R) →+* MvPolynomial (Fin m) R).comp
    (MvPolynomial.finSuccEquiv R m).toRingHom

theorem zeroHom_map (φ : R →+* S) (p : MvPolynomial (Fin (m+1)) R) :
    MvPolynomial.map φ (zeroHom R m p) = zeroHom S m (MvPolynomial.map φ p) := by
  have H : (MvPolynomial.map φ).comp (zeroHom R m) = (zeroHom S m).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [zeroHom, MvPolynomial.finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [zeroHom, MvPolynomial.finSuccEquiv_X_zero]
      · simp [zeroHom, MvPolynomial.finSuccEquiv_X_succ]
  exact congrArg (fun f : MvPolynomial (Fin (m+1)) R →+* MvPolynomial (Fin m) S => f p) H

noncomputable def zeroHead (p : Polynomial (MvPolynomial (Fin (m+1)) R)) :
    Polynomial (MvPolynomial (Fin (m+2)) R) :=
  p.map ((MvPolynomial.rename Fin.succ).toRingHom.comp
    ((MvPolynomial.rename Fin.succ).toRingHom.comp (zeroHom R m)))

noncomputable def epsilonHead (p : Polynomial (MvPolynomial (Fin (m+1)) R)) :
    Polynomial (MvPolynomial (Fin (m+2)) R) := p.map (MvPolynomial.rename Fin.succ).toRingHom

theorem zeroHead_map (φ : R →+* S) (p : Polynomial (MvPolynomial (Fin (m+1)) R)) :
    (zeroHead p).map (MvPolynomial.map φ) = zeroHead (p.map (MvPolynomial.map φ)) := by
  apply Polynomial.ext
  intro y
  simp only [zeroHead, Polynomial.coeff_map, RingHom.comp_apply]
  change MvPolynomial.map φ (MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ (zeroHom R m (p.coeff y)))) =
    MvPolynomial.rename Fin.succ (MvPolynomial.rename Fin.succ (zeroHom S m (MvPolynomial.map φ (p.coeff y))))
  rw [MvPolynomial.map_rename, MvPolynomial.map_rename, zeroHom_map]

theorem epsilonHead_map (φ : R →+* S) (p : Polynomial (MvPolynomial (Fin (m+1)) R)) :
    (epsilonHead p).map (MvPolynomial.map φ) = epsilonHead (p.map (MvPolynomial.map φ)) := by
  apply Polynomial.ext
  intro y
  simp only [epsilonHead, Polynomial.coeff_map]
  change MvPolynomial.map φ (MvPolynomial.rename Fin.succ (p.coeff y)) =
    MvPolynomial.rename Fin.succ (MvPolynomial.map φ (p.coeff y))
  exact MvPolynomial.map_rename _ _ _

theorem zeroHead_int (A : List Bool → ℕ)
    (p : (c : List Bool) → Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) :
    zeroHead (p c) = FixedWidthBivariateZeroLiftBits.head A p c := rfl

theorem epsilonHead_int (A : List Bool → ℕ)
    (p : (c : List Bool) → Polynomial (MvPolynomial (Fin (A c+1)) ℤ)) (c : List Bool) :
    epsilonHead (p c) = FixedWidthBivariateZeroLiftBits.epsilonHead A p c := rfl

end LeanCanny.Algebra.CoefficientTarskiZeroParameterQueries
