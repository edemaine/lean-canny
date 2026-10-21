/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ExactComplexTransport
public import LeanCanny.Algebra.KoszulComparisonInvariant

/-! # Simultaneous transport preserves the concrete Koszul comparison ratio

A graded equivalence intertwining both the coordinate-power differentials
and the input differentials identifies the concrete comparison ratios.
This isolates the coordinate-transport obligation for reordered systems;
the determinant comparison and its signs need no additional certificate.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {K : Type*} [Field K]

theorem comparisonRatio_eq_of_transport (p q : Fin n → Poly n K) (d e : Fin n → ℕ) (W Z : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hq : ∀ i, (q i).IsHomogeneous (e i))
    (hW : Macaulay.level d < 2 ^ W) (hZ : Macaulay.level e < 2 ^ Z)
    (hdetp : ∀ k, (powerComparisonMatrix p d W hp hW k).det ≠ 0)
    (hdetq : ∀ k, (powerComparisonMatrix q e Z hq hZ k).det ≠ 0)
    (T : (k : ℕ) → space (R := K) d (Macaulay.level d) W k ≃ₗ[K] space (R := K) e (Macaulay.level e) Z k)
    (hpower : ∀ k,
      (differential (Macaulay.powers (R := K) e) e (Macaulay.level e) Z (powers_homogeneous e) hZ k).comp
          (T (k + 1)).toLinearMap =
        (T k).toLinearMap.comp
          (differential (Macaulay.powers (R := K) d) d (Macaulay.level d) W (powers_homogeneous d) hW k))
    (hinput : ∀ k, (differential q e (Macaulay.level e) Z hq hZ k).comp (T (k + 1)).toLinearMap =
      (T k).toLinearMap.comp (differential p d (Macaulay.level d) W hp hW k)) :
    comparisonRatio p d W hp hW = comparisonRatio q e Z hq hZ := by
  have : Subsingleton (space (R := K) e (Macaulay.level e) Z (n + 1)) := by
    rw [space_eq_bot_of_lt e (Macaulay.level e) Z (n + 1) (by omega)]
    infer_instance
  let F := fun k => powerComparisonEquiv p d W hp hW k (hdetp k)
  let G := fun k => powerComparisonEquiv q e Z hq hZ k (hdetq k)
  have hF (k : ℕ) : (differential p d (Macaulay.level d) W hp hW k).comp (F (k + 1)).toLinearMap =
      (F k).toLinearMap.comp
        (differential (Macaulay.powers (R := K) d) d (Macaulay.level d) W (powers_homogeneous d) hW k) := by
    simp only [F, powerComparisonEquiv_toLinearMap]
    exact powerComparison_chain p d W hp hW k
  have hG (k : ℕ) : (differential q e (Macaulay.level e) Z hq hZ k).comp (G (k + 1)).toLinearMap =
      (G k).toLinearMap.comp
        (differential (Macaulay.powers (R := K) e) e (Macaulay.level e) Z (powers_homogeneous e) hZ k) := by
    simp only [G, powerComparisonEquiv_toLinearMap]
    exact powerComparison_chain q e Z hq hZ k
  have hi := ExactComplexTransport.comparison_invariant (K := K)
    (fun k => space (R := K) d (Macaulay.level d) W k) (fun k => space (R := K) e (Macaulay.level e) Z k)
    (differential (Macaulay.powers (R := K) d) d (Macaulay.level d) W (powers_homogeneous d) hW)
    (differential p d (Macaulay.level d) W hp hW)
    (differential (Macaulay.powers (R := K) e) e (Macaulay.level e) Z (powers_homogeneous e) hZ)
    (differential q e (Macaulay.level e) Z hq hZ) T F G hpower hinput hF hG
    (powers_weighted_exact e Z hZ) (powers_weighted_zero_surjective e Z hZ) n
  simp only [F, G, powerComparisonEquiv_toLinearMap] at hi
  rw [determinantRatio_powerComparison, determinantRatio_powerComparison] at hi
  exact hi

end LeanCanny.Algebra.KoszulWeighted
