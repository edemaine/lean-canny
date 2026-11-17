/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PolynomialBranchLimit

/-! # Leading-coefficient roots from filtered algebraic limits -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial Filter
open scoped Topology

/-- The parameter may tend to infinity along a subsequence or any nontrivial
filter; only eventual satisfaction of the polynomial equation is required. -/
theorem leadingCoefficient_root_of_filtered_limit {ι : Type*} {l : Filter ι} [NeBot l]
    (P : Polynomial (Polynomial ℤ)) (u t : ι → ℝ) (L : ℝ)
    (hu : Tendsto u l atTop) (ht : Tendsto t l (𝓝 L))
    (hroot : ∀ᶠ k in l, P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (t k)) (u k) = 0) :
    P.leadingCoeff.eval₂ (Int.castRingHom ℝ) L = 0 := by
  have hinv : Tendsto (fun k => (u k)⁻¹) l (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp hu
  have hc := (continuous_bivariate_integer_eval P.reverse).continuousAt.tendsto.comp (ht.prodMk_nhds hinv)
  have hz : ∀ᶠ k in l, P.reverse.eval₂
      (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (t k)) (u k)⁻¹ = 0 := by
    filter_upwards [hroot, hu.eventually_gt_atTop (0 : ℝ)] with k hk hku
    let := invertibleOfNonzero (ne_of_gt hku)
    simpa only [invOf_eq_inv] using
      (Polynomial.eval₂_reverse_eq_zero_iff
        (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (t k)) (u k) P).mpr hk
  have he := tendsto_nhds_unique hc (tendsto_const_nhds.congr' (hz.mono fun _ h => h.symm))
  simpa only [Polynomial.eval₂_at_zero, Polynomial.coeff_zero_reverse,
    Polynomial.coe_eval₂RingHom] using he

end LeanCanny.CountingHierarchy
