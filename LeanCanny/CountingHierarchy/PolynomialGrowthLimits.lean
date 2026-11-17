/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import LeanCanny.CountingHierarchy.PolynomialBranchLimit

/-! # Polynomial estimates for the fixed-power branch growth test -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial Filter Asymptotics
open scoped Topology

variable {ι : Type*} {l : Filter ι}

/-- A polynomial of degree at most `D`, evaluated at a divergent value between
zero and `v`, becomes negligible after division by any higher power of `v`. -/
theorem polynomial_scaled_eval_tendsto_zero (q : Polynomial ℝ) (D k : ℕ)
    (hD : q.natDegree ≤ D) (hk : D < k) (v t : ι → ℝ)
    (hv : Tendsto v l atTop) (ht : Tendsto t l atTop) (hbound : ∀ᶠ x in l, 0 ≤ t x ∧ t x ≤ v x) :
    Tendsto (fun x => q.eval (t x) / v x ^ k) l (𝓝 0) := by
  have htv : t =O[l] v := IsBigO.of_bound' (hbound.mono (fun x hx => by
    simp only [Real.norm_eq_abs, abs_of_nonneg hx.1, abs_of_nonneg (hx.1.trans hx.2)]
    exact hx.2))
  have hq : q.eval =O[atTop] (fun x : ℝ => x ^ D) := by
    have hd : q.degree ≤ (Polynomial.X ^ D : Polynomial ℝ).degree := by
      rw [Polynomial.degree_X_pow]
      exact Polynomial.degree_le_of_natDegree_le hD
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using q.isBigO_atTop_of_degree_le _ hd
  have hqv : (fun x => q.eval (t x)) =O[l] (fun x => v x ^ D) := (hq.comp_tendsto ht).trans (htv.pow D)
  have hsmall : (fun x : ℝ => x ^ D) =o[atTop] (fun x => x ^ k) := isLittleO_pow_pow_atTop_of_lt hk
  exact (hqv.trans_isLittleO (hsmall.comp_tendsto hv)).tendsto_div_nhds_zero

/-- A nonzero polynomial cannot approach zero along arguments tending to
positive infinity, including the nonzero constant case. -/
theorem polynomial_eval_not_tendsto_zero [NeBot l] (q : Polynomial ℝ) (hq : q ≠ 0)
    (t : ι → ℝ) (ht : Tendsto t l atTop) : ¬Tendsto (fun x => q.eval (t x)) l (𝓝 0) := by
  intro hz
  by_cases hd : 0 < q.degree
  · have hinf := (q.abs_tendsto_atTop hd).comp ht
    have hzero : Tendsto (fun x => |q.eval (t x)|) l (𝓝 (0 : ℝ)) := by simpa using hz.abs
    obtain ⟨x, hx, hx'⟩ := ((hinf.eventually_gt_atTop 1).and
      (hzero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)))).exists
    simp only [Function.comp_apply] at hx
    linarith
  · have he : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hd)
    have hz' := hz.congr' (Eventually.of_forall (fun x => congrArg (Polynomial.eval (t x)) he))
    have he0 : q.coeff 0 = 0 := tendsto_nhds_unique tendsto_const_nhds
      (by simpa only [Polynomial.eval_C] using hz')
    exact hq (he.trans (by rw [he0, Polynomial.C_0]))

end LeanCanny.CountingHierarchy
