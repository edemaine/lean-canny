/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayUniversalCancellation
public import LeanCanny.Algebra.MacaulayUniversalSpecialization

/-! # Macaulay extraneous determinants divide the numerators

The universal integer polynomial factorization extends to any commutative
coefficient ring and then specializes to each homogeneous system of
positive declared degrees. No domain or unique-factorization hypothesis
is imposed on the specialized ring. The standard characteristic pencils
inherit the same polynomial divisibility.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

theorem system_map_coefficients (φ : R →+* S) (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (system (R := R) d W π i).map (MvPolynomial.map φ) = system (R := S) d W π i := by
  unfold system
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · rw [MvPolynomial.map_monomial, MvPolynomial.map_X]
  · exact map_zero _

theorem numerator_map_coefficients (φ : R →+* S) (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n)) :
    MvPolynomial.map φ (numerator (R := R) d W π) = numerator (R := S) d W π := by
  rw [numerator, numerator, Macaulay.det_activeMinor_map]
  have hs : (fun i => (system (R := R) d W π i).map (MvPolynomial.map φ)) = system (R := S) d W π :=
    funext (system_map_coefficients φ d W π)
  rw [hs]

theorem denominator_map_coefficients (φ : R →+* S) (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n)) :
    MvPolynomial.map φ (denominator (R := R) d W π) = denominator (R := S) d W π := by
  rw [denominator, denominator, Macaulay.det_extraneousMinor_map]
  have hs : (fun i => (system (R := R) d W π i).map (MvPolynomial.map φ)) = system (R := S) d W π :=
    funext (system_map_coefficients φ d W π)
  rw [hs]

theorem denominator_dvd_numerator_any_ring (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W) (π : Equiv.Perm (Fin (n + 1))) :
    denominator (R := R) d W π ∣ numerator (R := R) d W π := by
  obtain ⟨q, hq⟩ := denominator_dvd_numerator (R := ℤ) d W hdegree hW π
  refine ⟨MvPolynomial.map (Int.castRingHom R) q, ?_⟩
  have he := congrArg (MvPolynomial.map (Int.castRingHom R)) hq
  rw [numerator_map_coefficients, map_mul, denominator_map_coefficients] at he
  exact he

end LeanCanny.Algebra.MacaulayUniversal

namespace LeanCanny.Algebra.Macaulay
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem extraneous_det_dvd_active_det (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : level d < 2 ^ W) :
    (extraneousMinor p d W).det ∣ (activeMinor p d W).det := by
  cases n with
  | zero =>
    rw [← eligibilityMinor_det_two, eligibilityMinor_det_eq_one p d W 2 (by omega)]
    exact one_dvd _
  | succ n =>
    exact MacaulayUniversal.specialize_divisibility d W p hp hd hW
      (MacaulayUniversal.denominator_dvd_numerator_any_ring d W (MacaulayUniversal.degree_lt_width d W hd hW) hW (Equiv.refl _))

theorem extraneous_characteristic_dvd_active_characteristic (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hW : level d < 2 ^ W) :
    (AffineCharacteristic.subtractiveMatrix (extraneousMinor p d W)).det ∣
      (AffineCharacteristic.subtractiveMatrix (activeMinor p d W)).det := by
  have he := extraneous_det_dvd_active_det (subtractiveSystem p d) d W
    (subtractiveSystem_homogeneous p d hp) hd hW
  rw [extraneousMinor_subtractiveSystem, activeMinor_subtractiveSystem] at he
  exact he

end LeanCanny.Algebra.Macaulay
