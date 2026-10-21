/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayPolynomialCancellation

/-! # A normalized universal integer quotient and its polynomial values

The common integer quotient is chosen from its proved unique normalized
factorization. Substituting the actual input coefficients gives a value
over any commutative ring, including specializations at which the
extraneous determinant vanishes. The value is natural in coefficient maps
and factors the actual Macaulay numerator.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

noncomputable def integerQuotient (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W) : CoefficientRing (n + 1) ℤ :=
  Classical.choose (exists_unique_ordering_quotient (R := ℤ) d W hdegree hW).exists

theorem integerQuotient_spec (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W) :
    (∀ π, numerator (R := ℤ) d W π = denominator d W π * integerQuotient d W hdegree hW) ∧
      MvPolynomial.eval (powerPoint (R := ℤ) d) (integerQuotient d W hdegree hW) = 1 :=
  Classical.choose_spec (exists_unique_ordering_quotient (R := ℤ) d W hdegree hW).exists

theorem integerQuotient_ne_zero (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W) : integerQuotient d W hdegree hW ≠ 0 := by
  intro hz
  have he := (integerQuotient_spec d W hdegree hW).2
  rw [hz, map_zero] at he
  exact zero_ne_one he

noncomputable def coefficientSpecialization (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) :
    CoefficientRing (n + 1) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) (fun v => (p v.1).coeff v.2)

theorem coefficientSpecialization_map (φ : R →+* S) (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) :
    φ.comp (coefficientSpecialization p) = coefficientSpecialization (fun i => (p i).map φ) := by
  rw [coefficientSpecialization, MvPolynomial.comp_eval₂Hom]
  have hcast : φ.comp (Int.castRingHom R) = Int.castRingHom S := Subsingleton.elim _ _
  rw [hcast, coefficientSpecialization]
  simp only [MvPolynomial.coeff_map]

theorem coefficientSpecialization_numerator (d : Fin (n + 1) → ℕ) (W : ℕ)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (hd : ∀ i, 0 < d i) (hW : Macaulay.level d < 2 ^ W) :
    coefficientSpecialization p (numerator (R := ℤ) d W (Equiv.refl _)) = (Macaulay.activeMinor p d W).det := by
  change MvPolynomial.eval₂ (Int.castRingHom R) (fun v : CoefficientIndex (n + 1) => (p v.1).coeff v.2) _ = _
  rw [MvPolynomial.eval₂_eq_eval_map, numerator_map_coefficients, specialize_numerator d W p hp hd hW]

theorem coefficientSpecialization_denominator (d : Fin (n + 1) → ℕ) (W : ℕ)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (hd : ∀ i, 0 < d i) (hW : Macaulay.level d < 2 ^ W) :
    coefficientSpecialization p (denominator (R := ℤ) d W (Equiv.refl _)) = (Macaulay.extraneousMinor p d W).det := by
  change MvPolynomial.eval₂ (Int.castRingHom R) (fun v : CoefficientIndex (n + 1) => (p v.1).coeff v.2) _ = _
  rw [MvPolynomial.eval₂_eq_eval_map, denominator_map_coefficients, specialize_denominator d W p hp hd hW]

noncomputable def polynomialValue (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) : R :=
  coefficientSpecialization p (integerQuotient d W hdegree hW)

theorem polynomialValue_map (φ : R →+* S) (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) :
    φ (polynomialValue d W hdegree hW p) = polynomialValue d W hdegree hW (fun i => (p i).map φ) :=
  RingHom.congr_fun (coefficientSpecialization_map φ p) _

theorem polynomialValue_factorization (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) :
    (Macaulay.activeMinor p d W).det = (Macaulay.extraneousMinor p d W).det * polynomialValue d W hdegree hW p := by
  have he := congrArg (coefficientSpecialization p) ((integerQuotient_spec d W hdegree hW).1 (Equiv.refl _))
  rw [coefficientSpecialization_numerator d W p hp hd hW, map_mul,
    coefficientSpecialization_denominator d W p hp hd hW] at he
  exact he

end LeanCanny.Algebra.MacaulayUniversal
