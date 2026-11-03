/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RelativeAffineGridValueGram
public import LeanCanny.Algebra.RelativeProjectiveValueScaling
public import LeanCanny.Algebra.HomogenizationAdditive
/-! # Coordinate and tested-row scales reach the actual affine Gram certificate -/
@[expose] public section
namespace LeanCanny.Algebra.RelativeAffineGridValueScaling
open Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem homogeneous_rows_scale {R : Type*} [CommRing R]
    (p : Fin n→Polynomial (Polynomial R)) (d : Fin n→ℕ) (a : Polynomial R) :
    AffineRingCoordinates.homogeneousRows (RelativeAffineGridValueGram.rows (fun i=>C a*p i)) d=
      fun i=>MvPolynomial.C a*AffineRingCoordinates.homogeneousRows (RelativeAffineGridValueGram.rows p) d i :=by
  funext i
  simp only [AffineRingCoordinates.homogeneousRows,RelativeAffineGridValueGram.rows,
    map_mul,Polynomial.toMvPolynomial_C,WeightedHomogenization.homogenize_C_mul,MvPolynomial.rename_C]

theorem test_scale {R : Type*} [CommRing R]
    (q : MvPolynomial (Fin n) (Polynomial R)) (e : ℕ) (s : Polynomial R) :
    RelativeAffineGridValueGram.test (MvPolynomial.C s*q) e=
      MvPolynomial.C s*RelativeAffineGridValueGram.test q e :=by
  simp only [RelativeAffineGridValueGram.test,WeightedHomogenization.homogenize_C_mul,
    map_mul,MvPolynomial.rename_C]

theorem trailing_degree_scale (p : Fin n→Polynomial (Polynomial ℝ))
    (q : MvPolynomial (Fin n) (Polynomial ℝ)) (d : Fin n→ℕ) (e : ℕ) (a s : ℝ)
    (ha : a≠0) (hs : s≠0)
    (hA : RelativeProjectiveValueGram.polynomial
      (AffineRingCoordinates.homogeneousRows (RelativeAffineGridValueGram.rows p) d)
      (RelativeAffineGridValueGram.test q e) d e (RelativeAffineGridValueGram.width d e)≠0) :
    (RelativeAffineGridValueGram.annihilator (fun i=>C (C a)*p i) (MvPolynomial.C (C s)*q) d e).natTrailingDegree=
      (RelativeAffineGridValueGram.annihilator p q d e).natTrailingDegree :=by
  unfold RelativeAffineGridValueGram.annihilator
  rw [homogeneous_rows_scale,test_scale]
  exact RelativeProjectiveValueScaling.trailing_degree_scale _ _ d e _ a s ha hs hA

theorem trailing_zero_scale (p : Fin n→Polynomial (Polynomial ℝ))
    (q : MvPolynomial (Fin n) (Polynomial ℝ)) (d : Fin n→ℕ) (e : ℕ) (a s : ℝ)
    (ha : a≠0) (hs : s≠0)
    (hA : RelativeProjectiveValueGram.polynomial
      (AffineRingCoordinates.homogeneousRows (RelativeAffineGridValueGram.rows p) d)
      (RelativeAffineGridValueGram.test q e) d e (RelativeAffineGridValueGram.width d e)≠0) (t : ℝ) :
    (RelativeAffineGridValueGram.annihilator (fun i=>C (C a)*p i) (MvPolynomial.C (C s)*q) d e).trailingCoeff.eval t=0 ↔
      (RelativeAffineGridValueGram.annihilator p q d e).trailingCoeff.eval t=0 :=by
  unfold RelativeAffineGridValueGram.annihilator
  rw [homogeneous_rows_scale,test_scale]
  exact RelativeProjectiveValueScaling.trailing_zero_scale _ _ d e _ a s ha hs hA t

end LeanCanny.Algebra.RelativeAffineGridValueScaling
