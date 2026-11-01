/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RelativeAffineGridValueGram

/-! # Actual relative value systems commute with coefficient maps

The coordinate embedding, homogeneous rows and reciprocal value equation
preserve their coefficients under arbitrary ring maps. No injectivity or
degree-preservation premise is required, including for nilpotent maps.
-/

@[expose] public section
namespace LeanCanny.Algebra.RelativeValueSystemMap
open Polynomial MvPolynomial
variable {R A : Type*} [CommRing R] [CommRing A]

theorem coordinate {σ : Type*} (φ : R →+* A) (p : Polynomial R) (i : σ) :
    (p.toMvPolynomial i).map φ = (p.map φ).toMvPolynomial i := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | monomial k a =>
    simp only [Polynomial.map_monomial, UnivariateInfinity.monomial, MvPolynomial.map_monomial]

theorem homogeneous {n : ℕ} (φ : R →+* A)
    (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (i : Fin n) :
    (AffineRingCoordinates.homogeneousRows p d i).map φ =
      AffineRingCoordinates.homogeneousRows (fun j => (p j).map φ) d i := by
  rw [AffineRingCoordinates.homogeneousRows, MvPolynomial.map_rename, WeightedHomogenization.map_homogenize]
  rfl

noncomputable def homogeneousTest {n : ℕ} (p : MvPolynomial (Fin n) R) (d : ℕ) :
    MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.rename (AffineFiniteCoordinates.layout n) (WeightedHomogenization.homogenize (fun _ => 1) d p)

theorem test {n : ℕ} (φ : R →+* A) (p : MvPolynomial (Fin n) R) (d : ℕ) :
    (homogeneousTest p d).map φ = homogeneousTest (p.map φ) d := by
  rw [homogeneousTest, MvPolynomial.map_rename, WeightedHomogenization.map_homogenize]
  rfl

theorem lift {σ : Type*} (φ : R →+* A) (p : MvPolynomial σ R) :
    (p.map Polynomial.C).map (Polynomial.mapRingHom φ) = (p.map φ).map Polynomial.C := by
  rw [MvPolynomial.map_map, MvPolynomial.map_map]
  have HH : (Polynomial.mapRingHom φ).comp Polynomial.C = Polynomial.C.comp φ := by
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
  exact congrArg (fun ψ : R →+* Polynomial A => p.map ψ) HH

noncomputable def reciprocal {n : ℕ}
    (H : Fin n → MvPolynomial (Fin (n + 1)) R) (p : MvPolynomial (Fin (n + 1)) R) (d : ℕ) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) (Polynomial R) :=
  Fin.cases (MvPolynomial.C Polynomial.X * p.map Polynomial.C - MvPolynomial.X 0 ^ d)
    (fun i => (H i).map Polynomial.C)

theorem system {n : ℕ} (φ : R →+* A)
    (H : Fin n → MvPolynomial (Fin (n + 1)) R) (p : MvPolynomial (Fin (n + 1)) R) (d : ℕ)
    (i : Fin (n + 1)) :
    (reciprocal H p d i).map (Polynomial.mapRingHom φ) =
      reciprocal (fun j => (H j).map φ) (p.map φ) d i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [reciprocal, Fin.cases_zero, map_sub, map_mul,
      MvPolynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_X, map_pow, MvPolynomial.map_X, lift]
  · simp only [reciprocal, Fin.cases_succ, lift]

theorem existing_system {n : ℕ} (φ : Polynomial R →+* A)
    (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (p : MvPolynomial (Fin (n + 1)) (Polynomial R)) (d : ℕ) (i : Fin (n + 1)) :
    (RelativeProjectiveValueGram.system H p d i).map (Polynomial.mapRingHom φ) =
      reciprocal (fun j => (H j).map φ) (p.map φ) d i := system φ H p d i

end LeanCanny.Algebra.RelativeValueSystemMap
