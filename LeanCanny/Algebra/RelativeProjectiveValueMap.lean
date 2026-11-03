/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RelativeValueSystemMap
/-! # The full relative Gram value certificate commutes with specialization

Matrix boxes and assigned degrees stay fixed. No injectivity, reducedness,
or preservation of specialized polynomial degrees is required.
-/
@[expose] public section
namespace LeanCanny.Algebra.RelativeProjectiveValueMap
open Polynomial
variable {n : ℕ} {R A : Type*} [CommRing R] [CommRing A]

theorem polynomial (φ : R→+*A)
    (H : Fin n→MvPolynomial (Fin (n+1)) (Polynomial R))
    (F : MvPolynomial (Fin (n+1)) (Polynomial R)) (d : Fin n→ℕ) (e W : ℕ) :
    (RelativeProjectiveValueGram.polynomial H F d e W).map (Polynomial.mapRingHom φ)=
      RelativeProjectiveValueGram.polynomial (fun i=>(H i).map (Polynomial.mapRingHom φ))
        (F.map (Polynomial.mapRingHom φ)) d e W :=by
  have HS : (fun i=>(RelativeProjectiveValueGram.system H F e i).map
      (Polynomial.mapRingHom (Polynomial.mapRingHom φ)))=
      RelativeProjectiveValueGram.system (fun i=>(H i).map (Polynomial.mapRingHom φ))
        (F.map (Polynomial.mapRingHom φ)) e :=by
    funext i
    exact RelativeValueSystemMap.system (Polynomial.mapRingHom φ) H F e i
  change (Polynomial.mapRingHom (Polynomial.mapRingHom φ))
    (RelativeProjectiveBoxGram.polynomial _ _ W)=_
  rw [RelativeProjectiveBoxGram.eval_polynomial,MacaulayFullBox.matrix_map,HS]
  rfl

theorem annihilator (φ : R→+*A)
    (H : Fin n→MvPolynomial (Fin (n+1)) (Polynomial R))
    (F : MvPolynomial (Fin (n+1)) (Polynomial R)) (d : Fin n→ℕ) (e W : ℕ) :
    (RelativeProjectiveValueGram.annihilator H F d e W).map (Polynomial.mapRingHom φ)=
      RelativeProjectiveValueGram.annihilator (fun i=>(H i).map (Polynomial.mapRingHom φ))
        (F.map (Polynomial.mapRingHom φ)) d e W :=by
  simp only [RelativeProjectiveValueGram.annihilator,Polynomial.map_mul,Polynomial.map_X]
  rw [←Polynomial.reflect_map,polynomial]

end LeanCanny.Algebra.RelativeProjectiveValueMap
