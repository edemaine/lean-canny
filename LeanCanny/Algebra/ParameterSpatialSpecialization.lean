/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectionCriticalFamily

/-! # Spatial critical equations with one retained parameter

Variable zero is a parameter. Specializing it commutes with all remaining
partial derivatives and with the actual spatial critical equations. The
parameter is never differentiated as a spatial coordinate.
-/

@[expose] public section
namespace LeanCanny.Algebra.ParameterSpatialSpecialization
open MvPolynomial
open scoped Classical
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

noncomputable def specialize (φ : R →+* S) (t : S) :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) S :=
  eval₂Hom (C.comp φ) (Fin.cons (C t) X)

theorem eval_specialize (φ : R →+* S) (t : S) (p : MvPolynomial (Fin (n + 1)) R) (y : Fin n → S) :
    (specialize φ t p).eval y = p.eval₂ φ (Fin.cons t y) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [specialize]
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, eval_mul, eval₂_mul, hp]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [specialize]

theorem specialize_pderiv (φ : R →+* S) (t : S) (p : MvPolynomial (Fin (n + 1)) R) (i : Fin n) :
    specialize φ t (pderiv i.succ p) = pderiv i (specialize φ t p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [specialize]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [pderiv_mul, map_add, map_mul, hp]
    congr 1
    congr 1
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [specialize]
    · simp [specialize, Pi.single_apply, Fin.succ_inj]

noncomputable def equation (p : MvPolynomial (Fin (n + 1)) R) (b : Fin n) (v : Fin n → R) (i : Fin n) :
    MvPolynomial (Fin (n + 1)) R :=
  if i = b then p else pderiv i.succ p - C (v i) * pderiv b.succ p

theorem specialize_equation (φ : R →+* S) (t : S) (p : MvPolynomial (Fin (n + 1)) R)
    (b : Fin n) (v : Fin n → R) (i : Fin n) :
    specialize φ t (equation p b v i) =
      ProjectionCriticalFamily.spatialEquation (specialize φ t p) b (fun j => φ (v j)) i := by
  by_cases hi : i = b
  · simp only [equation, ProjectionCriticalFamily.spatialEquation, hi, ite_true]
  · simp only [equation, ProjectionCriticalFamily.spatialEquation, hi, ite_false,
      map_sub, map_mul, specialize_pderiv]
    simp only [specialize, eval₂Hom_C, RingHom.comp_apply]

end LeanCanny.Algebra.ParameterSpatialSpecialization
