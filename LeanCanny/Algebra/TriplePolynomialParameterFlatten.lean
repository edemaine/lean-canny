/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.MvPolynomial.Equiv
/-! # Three retained polynomial parameters before a finite coefficient block

The variable order is outer parameter, middle parameter, inner parameter,
then the original coefficient variables. The map is an exact ring homomorphism,
so it can be applied to a normalized universal value before coefficient access.
-/
@[expose] public section
namespace LeanCanny.Algebra.TriplePolynomialParameterFlatten
open MvPolynomial
variable {a : ℕ} {R : Type*} [CommRing R]

noncomputable def one : Polynomial (MvPolynomial (Fin a) R) →+* MvPolynomial (Fin (a + 1)) R :=
  (finSuccEquiv R a).symm.toRingHom

noncomputable def two : Polynomial (Polynomial (MvPolynomial (Fin a) R)) →+*
    MvPolynomial (Fin (a + 2)) R :=
  one.comp (Polynomial.mapRingHom one)

noncomputable def flatten : Polynomial (Polynomial (Polynomial (MvPolynomial (Fin a) R))) →+*
    MvPolynomial (Fin (a + 3)) R :=
  one.comp (Polynomial.mapRingHom two)

noncomputable def exponent (s t r : ℕ) (v : Fin a →₀ ℕ) : Fin (a + 3) →₀ ℕ :=
  ((v.cons r).cons t).cons s

theorem one_coefficient (p : Polynomial (MvPolynomial (Fin a) R)) (k : ℕ) (v : Fin a →₀ ℕ) :
    (one p).coeff (v.cons k) = (p.coeff k).coeff v := by
  rw [← finSuccEquiv_coeff_coeff v (one p) k]
  change (((finSuccEquiv R a) ((finSuccEquiv R a).symm p)).coeff k).coeff v = _
  rw [AlgEquiv.apply_symm_apply]

theorem coefficient (p : Polynomial (Polynomial (Polynomial (MvPolynomial (Fin a) R))))
    (s t r : ℕ) (v : Fin a →₀ ℕ) :
    (flatten p).coeff (exponent s t r v) = (((p.coeff s).coeff t).coeff r).coeff v := by
  change (one ((p.map two))).coeff (((v.cons r).cons t).cons s) = _
  rw [one_coefficient, Polynomial.coeff_map]
  change (one (((p.coeff s).map one))).coeff ((v.cons r).cons t) = _
  rw [one_coefficient, Polynomial.coeff_map, one_coefficient]

end LeanCanny.Algebra.TriplePolynomialParameterFlatten
