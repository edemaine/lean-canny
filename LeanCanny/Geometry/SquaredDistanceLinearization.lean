/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.SquaredDistanceFibers
/-! # A single initial quadratic feature makes every radial constraint affine

The feature does not depend on the center. Consequently recursive frames
can retain their original polynomial degree and vary only affine heights.
-/
@[expose] public section
namespace LeanCanny.Geometry.SquaredDistanceLinearization
open Set
open scoped BigOperators
variable {n : ℕ}

def feature (x : Fin n → ℝ) : ℝ := ∑ i, x i^2

def affine (center : Fin n → ℝ) (v : ℝ) (x : Fin n → ℝ) : ℝ :=
  v-2*(∑ i, center i*x i)+(∑ i, center i^2)

theorem affine_feature (center x : Fin n → ℝ) :
    affine center (feature x) x=SquaredDistanceFibers.value center x := by
  have H : (∑ i, (x i-center i)^2)=
      (∑ i, (x i^2-2*(center i*x i)+center i^2)) :=
    Finset.sum_congr rfl (fun i _ => by ring)
  unfold affine feature SquaredDistanceFibers.value
  rw [H,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]

theorem affine_eq_radius (center x : Fin n → ℝ) (v r : ℝ) (hv : v=feature x) :
    affine center v x=r ↔ SquaredDistanceFibers.value center x=r := by
  rw [hv,affine_feature]

/-- Clearing a nonzero common denominator uses polynomial multiplication only. -/
theorem cleared_affine (center x : Fin n → ℝ) (q : ℝ) (hq : q≠0) (v r : ℝ)
    (hv : v=feature x) :
    q^2*v-2*(∑ i, (q*center i)*(q*x i))+(∑ i, (q*center i)^2)=q^2*r ↔
      SquaredDistanceFibers.value center x=r := by
  have H : q^2*v-2*(∑ i, (q*center i)*(q*x i))+(∑ i, (q*center i)^2)=
      q^2*affine center v x := by
    have HS : (∑ i, (q*center i)*(q*x i))=q^2*(∑ i, center i*x i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have HT : (∑ i, (q*center i)^2)=q^2*(∑ i, center i^2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [HS,HT]
    unfold affine
    ring
  rw [H]
  constructor
  · intro HE
    exact (affine_eq_radius center x v r hv).mp (mul_left_cancel₀ (pow_ne_zero 2 hq) HE)
  · intro HE
    rw [(affine_eq_radius center x v r hv).mpr HE]

end LeanCanny.Geometry.SquaredDistanceLinearization
