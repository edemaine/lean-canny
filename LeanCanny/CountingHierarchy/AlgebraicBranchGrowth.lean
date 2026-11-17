/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PolynomialGrowthLimits

/-! # A divergent algebraic branch cannot remain below the fixed-power scale -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial Filter
open scoped Topology BigOperators

/-- The leading parameter coefficient would tend to zero if a divergent
algebraic root remained between zero and `v` at parameter `v^(D+1)`. Reversal
makes all lower parameter coefficients negligible, contradicting nonvanishing. -/
theorem no_small_divergent_algebraic_branch {ι : Type*} {l : Filter ι} [NeBot l]
    (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0) (D : ℕ)
    (hdegree : ∀ j, (P.coeff j).natDegree ≤ D) (v t : ι → ℝ)
    (hv : Tendsto v l atTop) (ht : Tendsto t l atTop)
    (hbound : ∀ᶠ x in l, 0 ≤ t x ∧ t x ≤ v x)
    (hroot : ∀ᶠ x in l, P.eval₂ (Polynomial.evalRingHom (t x)) (v x ^ (D + 1)) = 0) : False := by
  let term := fun (j : ℕ) (x : ι) => (P.reverse.coeff (j + 1)).eval (t x) *
    ((v x ^ (D + 1))⁻¹) ^ (j + 1)
  have hterm (j : ℕ) : Tendsto (term j) l (𝓝 (0 : ℝ)) := by
    have hd : (P.reverse.coeff (j + 1)).natDegree ≤ D := by
      rw [Polynomial.coeff_reverse]
      exact hdegree _
    have hk : D < (D + 1) * (j + 1) := by nlinarith
    simpa only [term, div_eq_mul_inv, pow_mul, inv_pow] using
      polynomial_scaled_eval_tendsto_zero _ D ((D + 1) * (j + 1)) hd hk v t hv ht hbound
  let S : ι → ℝ := fun x => ∑ j ∈ Finset.range P.natDegree, term j x
  have hS : Tendsto S l (𝓝 (0 : ℝ)) := by
    have h := tendsto_finsetSum (Finset.range P.natDegree) (fun j _ => hterm j)
    simpa only [Finset.sum_const_zero] using h
  have hform (x : ι) : P.reverse.eval₂ (Polynomial.evalRingHom (t x)) ((v x ^ (D + 1))⁻¹) =
      S x + P.leadingCoeff.eval (t x) := by
    rw [Polynomial.eval₂_eq_sum_range' _ (by
      have := P.reverse_natDegree_le
      omega : P.reverse.natDegree < P.natDegree + 1) _, Finset.sum_range_succ']
    simp only [Polynomial.coeff_zero_reverse, pow_zero, mul_one, Polynomial.coe_evalRingHom]
    rfl
  have hlead : Tendsto (fun x => P.leadingCoeff.eval (t x)) l (𝓝 (0 : ℝ)) := by
    have hn : Tendsto (fun x => -S x) l (𝓝 (0 : ℝ)) := by simpa only [neg_zero] using hS.neg
    apply hn.congr'
    filter_upwards [hroot, hv.eventually_gt_atTop (0 : ℝ)] with x hx hvx
    have hnonzero : v x ^ (D + 1) ≠ 0 := pow_ne_zero _ hvx.ne'
    let := invertibleOfNonzero hnonzero
    have hr : P.reverse.eval₂ (Polynomial.evalRingHom (t x)) ((v x ^ (D + 1))⁻¹) = 0 := by
      simpa only [invOf_eq_inv] using
        (Polynomial.eval₂_reverse_eq_zero_iff (Polynomial.evalRingHom (t x)) (v x ^ (D + 1)) P).mpr hx
    rw [hform] at hr
    linarith
  exact polynomial_eval_not_tendsto_zero P.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hP) t ht hlead

end LeanCanny.CountingHierarchy
