/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RelativeProjectiveValueMap
/-! # The actual affine coordinate-grid certificate commutes with specialization -/
@[expose] public section
namespace LeanCanny.Algebra.RelativeAffineGridValueMap
open Polynomial
variable {n : ℕ} {R A : Type*} [CommRing R] [CommRing A]
set_option backward.isDefEq.respectTransparency false

theorem annihilator (φ : R→+*A) (p : Fin n→Polynomial (Polynomial R))
    (q : MvPolynomial (Fin n) (Polynomial R)) (d : Fin n→ℕ) (e : ℕ) :
    (RelativeAffineGridValueGram.annihilator p q d e).map (Polynomial.mapRingHom φ)=
      RelativeAffineGridValueGram.annihilator (fun i=>(p i).map (Polynomial.mapRingHom φ))
        (q.map (Polynomial.mapRingHom φ)) d e :=by
  have HH : (fun i=>(AffineRingCoordinates.homogeneousRows (RelativeAffineGridValueGram.rows p) d i).map
      (Polynomial.mapRingHom φ))=AffineRingCoordinates.homogeneousRows
        (RelativeAffineGridValueGram.rows (fun j=>(p j).map (Polynomial.mapRingHom φ))) d :=by
    have HR : (fun j=>(RelativeAffineGridValueGram.rows p j).map (Polynomial.mapRingHom φ))=
        RelativeAffineGridValueGram.rows (fun j=>(p j).map (Polynomial.mapRingHom φ)):=by
      funext j
      exact RelativeValueSystemMap.coordinate (Polynomial.mapRingHom φ) (p j) j
    funext i
    rw [RelativeValueSystemMap.homogeneous,HR]
  have HT : (RelativeAffineGridValueGram.test q e).map (Polynomial.mapRingHom φ)=
      RelativeAffineGridValueGram.test (q.map (Polynomial.mapRingHom φ)) e:=
    RelativeValueSystemMap.test (Polynomial.mapRingHom φ) q e
  unfold RelativeAffineGridValueGram.annihilator
  rw [RelativeProjectiveValueMap.annihilator,HH,HT]

end LeanCanny.Algebra.RelativeAffineGridValueMap
