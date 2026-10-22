/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulPowerComparison
public import LeanCanny.Algebra.MacaulayAlternatingFactors

/-! # The alternating comparison determinant is the Macaulay ratio

The product of positive odd-degree comparison determinants equals the
extraneous determinant times the positive even-degree product. Over a
field, nonzero comparison determinants identify their alternating quotient
with the active-numerator/extraneous-denominator ratio. Independence from
the chosen homotopy or input ordering is a separate obligation.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def comparisonOddProduct (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) : R :=
  ∏ k : Fin n, if Even k.val then (powerComparisonMatrix p d W hp hW (k.val + 1)).det else 1

noncomputable def comparisonEvenProduct (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) : R :=
  ∏ k : Fin n, if Even k.val then 1 else (powerComparisonMatrix p d W hp hW (k.val + 1)).det

theorem comparisonOddProduct_eq_extraneous_mul (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    comparisonOddProduct p d W hp hW = (Macaulay.extraneousMinor p d W).det * comparisonEvenProduct p d W hp hW := by
  simp only [comparisonOddProduct, comparisonEvenProduct, powerComparisonMatrix_det_succ]
  exact nonpivot_det_even_odd p d W hp hW

section Field
variable {K : Type*} [Field K]

noncomputable def comparisonRatio (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) : K :=
  (powerComparisonMatrix p d W hp hW 0).det * comparisonEvenProduct p d W hp hW /
    comparisonOddProduct p d W hp hW

theorem comparisonEvenProduct_ne_zero (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hdet : ∀ k : Fin n, (powerComparisonMatrix p d W hp hW (k.val + 1)).det ≠ 0) :
    comparisonEvenProduct p d W hp hW ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  by_cases hk : Even k.val
  · simp only [ite_eq_left hk, ne_eq, one_ne_zero, not_false_eq_true]
  · exact (ite_eq_right hk).trans_ne (hdet k)

theorem comparisonRatio_eq_macaulay (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hdet : ∀ k : Fin n, (powerComparisonMatrix p d W hp hW (k.val + 1)).det ≠ 0) :
    comparisonRatio p d W hp hW = (Macaulay.activeMinor p d W).det / (Macaulay.extraneousMinor p d W).det := by
  rw [comparisonRatio, powerComparisonMatrix_det_zero, comparisonOddProduct_eq_extraneous_mul]
  exact mul_div_mul_right _ _ (comparisonEvenProduct_ne_zero p d W hp hW hdet)

end Field
end LeanCanny.Algebra.KoszulWeighted
