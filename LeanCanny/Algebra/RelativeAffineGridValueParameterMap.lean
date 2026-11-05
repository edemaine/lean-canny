/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RelativeAffineGridValueMap
/-! # Joint parameter maps preserve the literal affine value certificate

A parameter map may mix radius and coefficient variables. It need not preserve
the old radius variable; only the separate value variable is retained.
-/
@[expose] public section
namespace LeanCanny.Algebra.RelativeAffineGridValueParameterMap
open Polynomial
variable {n : ℕ} {R A : Type*} [CommRing R] [CommRing A]
set_option backward.isDefEq.respectTransparency false

private theorem projective_polynomial (phi : Polynomial R →+* Polynomial A)
    (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (d : Fin n → ℕ) (e W : ℕ) :
    (RelativeProjectiveValueGram.polynomial H F d e W).map phi =
      RelativeProjectiveValueGram.polynomial (fun i => (H i).map phi) (F.map phi) d e W := by
  have HS : (fun i => (RelativeProjectiveValueGram.system H F e i).map (Polynomial.mapRingHom phi)) =
      RelativeProjectiveValueGram.system (fun i => (H i).map phi) (F.map phi) e := by
    funext i
    exact RelativeValueSystemMap.system phi H F e i
  change (Polynomial.mapRingHom phi) (RelativeProjectiveBoxGram.polynomial _ _ W) = _
  rw [RelativeProjectiveBoxGram.eval_polynomial, MacaulayFullBox.matrix_map, HS]
  rfl

private theorem projective_annihilator (phi : Polynomial R →+* Polynomial A)
    (H : Fin n → MvPolynomial (Fin (n + 1)) (Polynomial R))
    (F : MvPolynomial (Fin (n + 1)) (Polynomial R)) (d : Fin n → ℕ) (e W : ℕ) :
    (RelativeProjectiveValueGram.annihilator H F d e W).map phi =
      RelativeProjectiveValueGram.annihilator (fun i => (H i).map phi) (F.map phi) d e W := by
  simp only [RelativeProjectiveValueGram.annihilator, Polynomial.map_mul, Polynomial.map_X]
  rw [← Polynomial.reflect_map, projective_polynomial]

theorem annihilator (phi : Polynomial R →+* Polynomial A) (p : Fin n → Polynomial (Polynomial R))
    (q : MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ) (e : ℕ) :
    (RelativeAffineGridValueGram.annihilator p q d e).map phi =
      RelativeAffineGridValueGram.annihilator (fun i => (p i).map phi) (q.map phi) d e := by
  have HH : (fun i => (AffineRingCoordinates.homogeneousRows (RelativeAffineGridValueGram.rows p) d i).map phi) =
      AffineRingCoordinates.homogeneousRows
        (RelativeAffineGridValueGram.rows (fun j => (p j).map phi)) d := by
    have HR : (fun j => (RelativeAffineGridValueGram.rows p j).map phi) =
        RelativeAffineGridValueGram.rows (fun j => (p j).map phi) := by
      funext j
      exact RelativeValueSystemMap.coordinate phi (p j) j
    funext i
    rw [RelativeValueSystemMap.homogeneous, HR]
  have HT : (RelativeAffineGridValueGram.test q e).map phi =
      RelativeAffineGridValueGram.test (q.map phi) e := RelativeValueSystemMap.test phi q e
  unfold RelativeAffineGridValueGram.annihilator
  rw [projective_annihilator, HH, HT]

end LeanCanny.Algebra.RelativeAffineGridValueParameterMap
