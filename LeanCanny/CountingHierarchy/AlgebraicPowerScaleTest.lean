/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.AlgebraicBranchGrowth

/-! # A fixed-power test separates bounded and divergent algebraic branches -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial Filter Set
open scoped Topology

/-- A divergent nonnegative algebraic branch eventually exceeds `v` when
its parameter is `v^(D+1)`, where `D` bounds the degree in the branch value. -/
theorem divergent_algebraic_branch_power_gt (P : Polynomial (Polynomial ℝ)) (hP : P ≠ 0)
    (D : ℕ) (hdegree : ∀ j, (P.coeff j).natDegree ≤ D) (m : ℝ → ℝ)
    (hm : Tendsto m atTop atTop) (hmn : ∀ u : ℝ, 0 ≤ u → 0 ≤ m u)
    (hroot : ∀ u : ℝ, 0 < u → P.eval₂ (Polynomial.evalRingHom (m u)) u = 0) :
    ∀ᶠ v : ℝ in atTop, v < m (v ^ (D + 1)) := by
  by_contra hn
  have hfreq : ∃ᶠ v : ℝ in atTop, m (v ^ (D + 1)) ≤ v := by
    simpa only [not_lt] using (not_eventually.mp hn)
  let l : Filter ℝ := atTop ⊓ 𝓟 {v : ℝ | m (v ^ (D + 1)) ≤ v}
  let : NeBot l := frequently_iff_neBot.mp hfreq
  have hv : Tendsto (fun v : ℝ => v) l atTop := tendsto_id.mono_left inf_le_left
  have hpow : Tendsto (fun v : ℝ => v ^ (D + 1)) l atTop :=
    (tendsto_pow_atTop (Nat.succ_ne_zero D)).mono_left inf_le_left
  have ht : Tendsto (fun v : ℝ => m (v ^ (D + 1))) l atTop := hm.comp hpow
  have hsmall : ∀ᶠ v in l, m (v ^ (D + 1)) ≤ v := by
    apply Filter.Eventually.filter_mono (show l ≤ 𝓟 {v : ℝ | m (v ^ (D + 1)) ≤ v} from inf_le_right)
    exact eventually_principal.mpr (fun _ h => h)
  have hb : ∀ᶠ v in l, 0 ≤ m (v ^ (D + 1)) ∧ m (v ^ (D + 1)) ≤ v := by
    filter_upwards [hsmall, hv.eventually_ge_atTop 0] with v hvsmall hvpos
    exact ⟨hmn _ (pow_nonneg hvpos _), hvsmall⟩
  apply no_small_divergent_algebraic_branch P hP D hdegree (fun v => v)
    (fun v => m (v ^ (D + 1))) hv ht hb
  filter_upwards [hv.eventually_gt_atTop 0] with v hvpos
  exact hroot _ (pow_pos hvpos _)

/-- A bounded branch eventually lies strictly below the same comparison
scale. This direction needs no algebraic equation or continuity. -/
theorem bounded_branch_power_lt (D : ℕ) (m : ℝ → ℝ)
    (hb : ∃ B : ℝ, ∀ u : ℝ, 0 ≤ u → m u ≤ B) :
    ∀ᶠ v : ℝ in atTop, m (v ^ (D + 1)) < v := by
  obtain ⟨B, hB⟩ := hb
  filter_upwards [eventually_gt_atTop B, eventually_ge_atTop (0 : ℝ)] with v hvB hvpos
  exact (hB _ (pow_nonneg hvpos _)).trans_lt hvB

end LeanCanny.CountingHierarchy
