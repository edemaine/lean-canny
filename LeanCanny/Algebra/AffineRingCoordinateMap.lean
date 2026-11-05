/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RelativeValueSystemMap
/-! # Coefficient maps of the actual complete affine coordinate certificates

The declared degrees and fixed reciprocal reflection length are unchanged.
No injectivity or preservation of an actual polynomial degree is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.AffineRingCoordinateMap
open Polynomial MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {R A : Type*} [CommRing R] [CommRing A]

theorem system (φ : R →+* A) (H : Fin n → MvPolynomial (Fin (n + 1)) R)
    (coordinate : Fin (n + 1)) (i : Fin (n + 1)) :
    (AffineRingGramEliminant.system H coordinate i).map (Polynomial.mapRingHom φ) =
      AffineRingGramEliminant.system (fun j => (H j).map φ) coordinate i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [AffineRingGramEliminant.system, Fin.cases_zero, map_sub, map_mul,
      MvPolynomial.map_C, Polynomial.coe_mapRingHom, Polynomial.map_X, MvPolynomial.map_X]
  · exact RelativeValueSystemMap.lift φ (H j)

theorem polynomial (φ : R →+* A) (H : Fin n → MvPolynomial (Fin (n + 1)) R)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) :
    (AffineRingGramEliminant.polynomial H d W coordinate).map φ =
      AffineRingGramEliminant.polynomial (fun j => (H j).map φ) d W coordinate := by
  have hs : (fun i => (AffineRingGramEliminant.system H coordinate i).map (Polynomial.mapRingHom φ)) =
      AffineRingGramEliminant.system (fun j => (H j).map φ) coordinate :=
    funext (system φ H coordinate)
  change (Polynomial.mapRingHom φ) (AffineRingGramEliminant.polynomial H d W coordinate) = _
  rw [AffineRingGramEliminant.eval_polynomial, hs]
  rfl

theorem reciprocal (φ : R →+* A) (H : Fin n → MvPolynomial (Fin (n + 1)) R)
    (d : Fin n → ℕ) (W : ℕ) (coordinate : Fin (n + 1)) :
    (AffineRingGramEliminant.annihilator H d W coordinate).map φ =
      AffineRingGramEliminant.annihilator (fun j => (H j).map φ) d W coordinate := by
  simp only [AffineRingGramEliminant.annihilator, Polynomial.map_mul, Polynomial.map_X]
  rw [← Polynomial.reflect_map, polynomial]

theorem annihilator (φ : R →+* A) (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (coordinate : Fin n) :
    (AffineRingCoordinates.annihilator p d coordinate).map φ =
      AffineRingCoordinates.annihilator (fun j => (p j).map φ) d coordinate := by
  have hh : (fun i => (AffineRingCoordinates.homogeneousRows p d i).map φ) =
      AffineRingCoordinates.homogeneousRows (fun j => (p j).map φ) d :=
    funext (RelativeValueSystemMap.homogeneous φ p d)
  unfold AffineRingCoordinates.annihilator
  rw [reciprocal, hh]

end LeanCanny.Algebra.AffineRingCoordinateMap
