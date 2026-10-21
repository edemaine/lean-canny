/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Common divisors of maximal minors of a surjective matrix

Row multilinearity expands a rectangular product determinant in all full
row minors. If the row map is surjective, it has a matrix right section,
so any common divisor of these maximal minors divides one and is a unit.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixMaximalMinorSpan
open scoped Classical Matrix BigOperators
variable {R S T : Type*} [CommRing R] [Fintype S] [Fintype T] [DecidableEq T]

theorem det_mul_expansion (B : Matrix T S R) (D : Matrix S T R) :
    (B * D).det = ∑ f : T → S, (∏ t, B t (f t)) * (D.submatrix f id).det := by
  let F : MultilinearMap R (fun _ : T => T → R) R := Matrix.detRowAlternating.toMultilinearMap
  have hm : (fun t => (B * D : Matrix T T R) t) = (fun t => ∑ s, B t s • D s) := by
    funext t u
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change F (fun t => (B * D : Matrix T T R) t) = _
  rw [hm, F.map_sum]
  apply Finset.sum_congr rfl
  intro f _
  have he := F.map_smul_univ (fun t => B t (f t)) (fun t => D (f t))
  rw [show F (fun t => D (f t)) = (D.submatrix f id).det by rfl] at he
  simpa only [smul_eq_mul] using he

theorem dvd_det_mul (B : Matrix T S R) (D : Matrix S T R) (q : R)
    (hq : ∀ f : T → S, q ∣ (D.submatrix f id).det) : q ∣ (B * D).det := by
  rw [det_mul_expansion]
  apply Finset.dvd_sum
  intro f _
  exact dvd_mul_of_dvd_right (hq f) _

theorem isUnit_of_dvd_maximal_minors_of_surjective (D : Matrix S T R) (q : R)
    (hq : ∀ f : T → S, q ∣ (D.submatrix f id).det)
    (hsurj : Function.Surjective (fun v => Matrix.vecMul v D)) : IsUnit q := by
  let B : Matrix T S R := fun t => Classical.choose (hsurj (Pi.single t 1))
  have hB : B * D = 1 := by
    funext t u
    change Matrix.vecMul (B t) D u = (1 : Matrix T T R) t u
    have he := congrFun (Classical.choose_spec (hsurj (Pi.single t 1))) u
    simpa only [B, Pi.single_apply, Matrix.one_apply, eq_comm] using he
  apply isUnit_of_dvd_one
  have he := dvd_det_mul B D q hq
  rwa [hB, Matrix.det_one] at he

end LeanCanny.Algebra.MatrixMaximalMinorSpan
