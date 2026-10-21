/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayBinomialFactors
public import LeanCanny.Algebra.BinomialParityProducts

/-! # Alternating higher factors leave precisely the extraneous minor

The even-degree nonpivot determinant product equals the extraneous
determinant times the odd-degree product. This polynomial identity holds
over every commutative ring; no cancellation or division is used.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem eligibilityMinor_zero_exponent_product (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ) :
    (∏ j : Fin n, (Macaulay.eligibilityMinor p d W (j.val + 2)).det ^ (if j.val = 0 then 1 else 0)) =
      (Macaulay.extraneousMinor p d W).det := by
  rw [← Macaulay.eligibilityMinor_det_two]
  cases n with
  | zero =>
    rw [Fin.prod_univ_zero, Macaulay.eligibilityMinor_det_eq_one p d W 2 (by omega)]
  | succ n =>
    have he : (∏ j : Fin (n + 1), (Macaulay.eligibilityMinor p d W (j.val + 2)).det ^ (if j.val = 0 then 1 else 0)) =
        ∏ j : Fin (n + 1), if j = 0 then (Macaulay.eligibilityMinor p d W (j.val + 2)).det else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j = 0
      · simp [hj]
      · have hv : j.val ≠ 0 := fun hv => hj (Fin.ext hv)
        simp [hj, hv]
    rw [he, Fintype.prod_ite_eq']
    rfl

theorem nonpivot_det_even_odd (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (∏ k : Fin n, if Even k.val then (nonpivotContractionBlock p d W hp hW k.val).det else 1) =
      (Macaulay.extraneousMinor p d W).det *
        ∏ k : Fin n, if Even k.val then 1 else (nonpivotContractionBlock p d W hp hW k.val).det := by
  have he := BinomialParityProducts.binomial_even_odd_product n
    (fun j => (Macaulay.eligibilityMinor p d W (j.val + 2)).det)
  simp_rw [← nonpivotContractionBlock_det_binomial p d W hp hW] at he
  rw [eligibilityMinor_zero_exponent_product] at he
  exact he

end LeanCanny.Algebra.KoszulWeighted
