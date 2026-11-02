/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FlatAffineCriticalExtremum
public import LeanCanny.Algebra.PhysicalPowerCriticalCone

/-! # A free nonzero partial makes coordinate-slice constraints surjective

A variation in the unused coordinate corrects the source derivative while
preserving every active coordinate height. This proves the precise regularity
premise of the constrained-extremum theorem, without a critical Hessian test.
-/
@[expose] public section
namespace LeanCanny.Geometry.FlatCoordinateConstraintRegularity
open LeanCanny.Algebra FlatAffineCriticalExtremum MvPolynomial
open scoped Classical
variable {n : ℕ}

theorem derivative_some (p : MvPolynomial (Fin (n+1)) ℤ) (s : Finset (Fin (n+1)))
    (b : ℤ) (c : Fin (n+1) → ℤ) (free : Fin (n+1)) (z w : Fin (n+1) → ℝ) (j : s) :
    derivative (Int.castRingHom ℝ) p s (PhysicalPowerCriticalRows.coordinateNormals b c free) z w (some j)=
      (c j.val:ℝ)*w j.val := by
  simp only [derivative,ContinuousLinearMap.pi_apply,constraint,PolynomialCalculus.derivative_apply,height_partial]
  have H := PhysicalPowerCriticalRows.normal_height_sum (Int.castRingHom ℝ) b c free j.val w 1
  simpa only [pow_one,Int.coe_castRingHom] using H

theorem derivative_none (p : MvPolynomial (Fin (n+1)) ℤ) (s : Finset (Fin (n+1)))
    (b : ℤ) (c : Fin (n+1) → ℤ) (free : Fin (n+1)) (z w : Fin (n+1) → ℝ) :
    derivative (Int.castRingHom ℝ) p s (PhysicalPowerCriticalRows.coordinateNormals b c free) z w none=
      PolynomialCalculus.derivative (Int.castRingHom ℝ) p z w := by
  simp only [derivative,ContinuousLinearMap.pi_apply,constraint]

theorem surjective (p : MvPolynomial (Fin (n+1)) ℤ) (s : Finset (Fin (n+1)))
    (b : ℤ) (c : Fin (n+1) → ℤ) (hc : ∀ i, c i≠0) (free v : Fin (n+1)) (hv : v∉s)
    (z : Fin (n+1) → ℝ) (hp : (pderiv v p).eval₂ (Int.castRingHom ℝ) z≠0) :
    Function.Surjective (derivative (Int.castRingHom ℝ) p s (PhysicalPowerCriticalRows.coordinateNormals b c free) z) := by
  intro target
  let w : Fin (n+1) → ℝ := fun i => if hi : i∈s then target (some ⟨i,hi⟩)/(c i:ℝ) else 0
  let L := PolynomialCalculus.derivative (Int.castRingHom ℝ) p z
  let t := (target none-L w)/(pderiv v p).eval₂ (Int.castRingHom ℝ) z
  refine ⟨w+t • Pi.single v 1,?_⟩
  funext i
  cases i with
  | none =>
    rw [derivative_none]
    simp only [map_add,map_smul,smul_eq_mul,PolynomialCalculus.derivative_single]
    change L w+((target none-L w)/(pderiv v p).eval₂ (Int.castRingHom ℝ) z)*
      (pderiv v p).eval₂ (Int.castRingHom ℝ) z=target none
    rw [div_mul_cancel₀ _ hp]
    ring
  | some j =>
    rw [derivative_some]
    have HN : j.val≠v := by intro HE; exact hv (HE ▸ j.property)
    simp only [Pi.add_apply,Pi.smul_apply,Pi.single_apply,HN,ite_false,smul_eq_mul,mul_zero,add_zero,w,dite_eq_left j.property]
    change (c j.val:ℝ)*(target (some j)/(c j.val:ℝ))=target (some j)
    exact mul_div_cancel₀ _ (Int.cast_ne_zero.mpr (hc j.val))

end LeanCanny.Geometry.FlatCoordinateConstraintRegularity
