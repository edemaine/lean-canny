/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientCoordinateBasisSpecialization
public import LeanCanny.Algebra.SelectedMultivariatePolynomialLift
/-! # Actual selected coefficient lifts over a varying coefficient base -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientSelectedMultivariateLift
open Polynomial
open scoped Classical
variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B] {m N : ℕ}

noncomputable def lift (p : Polynomial (Polynomial A)) (representative : A → MvPolynomial (Fin m) R)
    (d e : ℕ) : Polynomial (MvPolynomial (Fin (m+1)) R) :=
  (SelectedParameterPolynomialLift.lift p representative d e).map (MvPolynomial.finSuccEquiv R m).symm.toRingHom

theorem coefficient (p : Polynomial (Polynomial A)) (representative : A → MvPolynomial (Fin m) R)
    (d e y k : ℕ) (v : Fin m →₀ ℕ) :
    ((lift p representative d e).coeff y).coeff (v.cons k) =
      if y ≤ d then if k ≤ e then (representative ((p.coeff y).coeff k)).coeff v else 0 else 0 := by
  rw [lift, Polynomial.coeff_map, ← MvPolynomial.finSuccEquiv_coeff_coeff]
  change (((MvPolynomial.finSuccEquiv R m) ((MvPolynomial.finSuccEquiv R m).symm
    ((SelectedParameterPolynomialLift.lift p representative d e).coeff y))).coeff k).coeff v = _
  rw [AlgEquiv.apply_symm_apply]
  change (((SelectedPolynomialLift.lift p (fun q => SelectedPolynomialLift.lift q representative e) d).coeff y).coeff k).coeff v = _
  rw [SelectedPolynomialLift.coefficient]
  by_cases hy : y ≤ d
  · rw [ite_eq_left hy, SelectedPolynomialLift.coefficient]
    by_cases hk : k ≤ e
    · rw [ite_eq_left hk, ite_eq_left hy, ite_eq_left hk]
    · rw [ite_eq_right hk, ite_eq_left hy, ite_eq_right hk]
      rfl
  · rw [ite_eq_right hy, ite_eq_right hy]
    rfl

/-- The finite advertised truncations survive maps that kill leading coefficients. -/
theorem map (φ : R →+* S) (ψ : A →+* B) (p : Polynomial (Polynomial A))
    (r : A → MvPolynomial (Fin m) R) (s : B → MvPolynomial (Fin m) S)
    (H : ∀ a, MvPolynomial.map φ (r a) = s (ψ a)) (d e : ℕ) :
    (lift p r d e).map (MvPolynomial.map φ) =
      lift (p.map (Polynomial.mapRingHom ψ)) s d e := by
  apply Polynomial.ext
  intro y
  apply MvPolynomial.ext
  intro v
  rw [← Finsupp.cons_tail v]
  rw [Polynomial.coeff_map, MvPolynomial.coeff_map, coefficient, coefficient]
  by_cases hy : y ≤ d
  · rw [ite_eq_left hy, ite_eq_left hy]
    by_cases hk : v 0 ≤ e
    · rw [ite_eq_left hk, ite_eq_left hk]
      simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
      exact congrArg (fun q => q.coeff (Finsupp.tail v)) (H ((p.coeff y).coeff (v 0)))
    · rw [ite_eq_right hk, ite_eq_right hk, map_zero]
  · rw [ite_eq_right hy, ite_eq_right hy, map_zero]

theorem lift_int (p : Polynomial (Polynomial A)) (r : A → MvPolynomial (Fin m) ℤ) (d e : ℕ) :
    lift p r d e = SelectedMultivariatePolynomialLift.lift p r d e := rfl

private theorem substitute_map {σ : Type*} (φ : R →+* S) (w : σ → ℕ) (p : MvPolynomial σ R) :
    MvPolynomial.map φ (CoordinatePowerSubstitution.substitute w p) =
      CoordinatePowerSubstitution.substitute w (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [CoordinatePowerSubstitution.substitute_C, MvPolynomial.map_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, CoordinatePowerSubstitution.substitute_X, map_pow,
      MvPolynomial.map_X, hp]

noncomputable def powered [Algebra R A] (b : CoefficientCoordinateBasis R A m N)
    (w : Fin m → ℕ) (p : Polynomial (Polynomial A)) (d e : ℕ) :=
  lift p (fun a => CoordinatePowerSubstitution.substitute w (b.representative a)) d e

theorem powered_map [Algebra R A] [Algebra S B] (φ : R →+* S) (ψ : A →+* B)
    {b : CoefficientCoordinateBasis R A m N} {c : CoefficientCoordinateBasis S B m N}
    (H : b.Specializes φ ψ c) (w : Fin m → ℕ) (p : Polynomial (Polynomial A)) (d e : ℕ) :
    (powered b w p d e).map (MvPolynomial.map φ) =
      powered c w (p.map (Polynomial.mapRingHom ψ)) d e := by
  apply map
  intro a
  rw [substitute_map, H.representative_map]

theorem powered_ofIntegral (b : IntegralCoordinateBasis A m N) (w : Fin m → ℕ)
    (p : Polynomial (Polynomial A)) (d e : ℕ) :
    powered (CoefficientCoordinateBasis.ofIntegral b) w p d e =
      SelectedMultivariatePolynomialLift.lift p (SelectedPoweredPolynomialLift.representative b w) d e := rfl

end LeanCanny.Algebra.CoefficientSelectedMultivariateLift
