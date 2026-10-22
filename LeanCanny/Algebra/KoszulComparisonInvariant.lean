/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ExactComplexComparison
public import LeanCanny.Algebra.KoszulPowerComparisonSpecialization
public import LeanCanny.Algebra.KoszulComparisonRatio

/-! # The Koszul ratio is independent of the chain comparison

Every degreewise equivalence from the finite coordinate-power complex to
the input complex has the same alternating determinant as the explicit
power comparison. Thus it computes the same Macaulay ratio. Transport
between simultaneously reordered input/spatial coordinates remains a
separate step.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical Matrix
variable {n : ℕ} {K : Type*} [Field K]

theorem powerComparison_det (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (powerComparison p d W hp hW k).det = (powerComparisonMatrix p d W hp hW k).det := by
  rw [powerComparisonMatrix, Matrix.det_transpose, LinearMap.det_toMatrix]

theorem determinantRatio_powerComparison (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    ExactComplexComparison.determinantRatio (fun k => space (R := K) d (Macaulay.level d) W k)
      (powerComparison p d W hp hW) n = comparisonRatio p d W hp hW := by
  unfold ExactComplexComparison.determinantRatio AlternatingProducts.ratio
  simp_rw [powerComparison_det]
  have hzero : Even (0 : ℕ) := ⟨0, rfl⟩
  have he : AlternatingProducts.evenProduct (fun k => (powerComparisonMatrix p d W hp hW k).det) (n + 1) =
      (powerComparisonMatrix p d W hp hW 0).det * comparisonEvenProduct p d W hp hW := by
    rw [AlternatingProducts.evenProduct, Finset.prod_range_succ']
    simp only [hzero, ite_true, Nat.even_add_one, ite_not]
    rw [comparisonEvenProduct, Fin.prod_univ_eq_prod_range
      (fun k => if Even k then 1 else (powerComparisonMatrix p d W hp hW (k + 1)).det) n]
    exact mul_comm _ _
  have ho : AlternatingProducts.oddProduct (fun k => (powerComparisonMatrix p d W hp hW k).det) (n + 1) =
      comparisonOddProduct p d W hp hW := by
    rw [AlternatingProducts.oddProduct, Finset.prod_range_succ']
    simp only [hzero, ite_true, mul_one, Nat.even_add_one, ite_not]
    rw [comparisonOddProduct, Fin.prod_univ_eq_prod_range
      (fun k => if Even k then (powerComparisonMatrix p d W hp hW (k + 1)).det else 1) n]
  rw [he, ho]
  rfl

theorem determinantRatio_eq_comparisonRatio (p : Fin n → Poly n K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (hdet : ∀ k, (powerComparisonMatrix p d W hp hW k).det ≠ 0)
    (G : (k : ℕ) → space (R := K) d (Macaulay.level d) W k ≃ₗ[K] space (R := K) d (Macaulay.level d) W k)
    (hG : ∀ k, (differential p d (Macaulay.level d) W hp hW k).comp (G (k + 1)).toLinearMap =
      (G k).toLinearMap.comp
        (differential (Macaulay.powers (R := K) d) d (Macaulay.level d) W (powers_homogeneous d) hW k)) :
    ExactComplexComparison.determinantRatio (fun k => space (R := K) d (Macaulay.level d) W k)
      (fun k => (G k).toLinearMap) n = comparisonRatio p d W hp hW := by
  have : Subsingleton (space (R := K) d (Macaulay.level d) W (n + 1)) := by
    rw [space_eq_bot_of_lt d (Macaulay.level d) W (n + 1) (by omega)]
    infer_instance
  let F := fun k => powerComparisonEquiv p d W hp hW k (hdet k)
  have hF (k : ℕ) : (differential p d (Macaulay.level d) W hp hW k).comp (F (k + 1)).toLinearMap =
      (F k).toLinearMap.comp
        (differential (Macaulay.powers (R := K) d) d (Macaulay.level d) W (powers_homogeneous d) hW k) := by
    simp only [F, powerComparisonEquiv_toLinearMap]
    exact powerComparison_chain p d W hp hW k
  have he := ExactComplexComparison.comparison_invariant (K := K)
    (fun k => space (R := K) d (Macaulay.level d) W k)
    (differential (Macaulay.powers (R := K) d) d (Macaulay.level d) W (powers_homogeneous d) hW)
    (differential p d (Macaulay.level d) W hp hW) F G hF hG
    (powers_weighted_exact d W hW) (powers_weighted_zero_surjective d W hW) n
  simp only [F, powerComparisonEquiv_toLinearMap] at he
  exact he.symm.trans (determinantRatio_powerComparison p d W hp hW)

end LeanCanny.Algebra.KoszulWeighted
