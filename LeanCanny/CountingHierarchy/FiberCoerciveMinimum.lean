/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ParameterizedCoerciveMinimum

/-! # Continuous fiber minima and divergence at empty fibers -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Set Filter
open scoped Topology

theorem monotoneOn_unbounded_iff_tendsto (m : ℝ → ℝ) (hm : MonotoneOn m (Ici 0)) :
    (¬∃ B : ℝ, ∀ u : ℝ, 0 ≤ u → m u ≤ B) ↔ Tendsto m atTop atTop := by
  constructor
  · intro hb
    apply tendsto_atTop.mpr
    intro B
    have hex : ∃ u : ℝ, 0 ≤ u ∧ B < m u := by
      by_contra hn
      apply hb
      refine ⟨B, fun u hu => ?_⟩
      by_contra hle
      exact hn ⟨u, hu, lt_of_not_ge hle⟩
    obtain ⟨u, hu, hBu⟩ := hex
    filter_upwards [eventually_ge_atTop u] with v hv
    exact hBu.le.trans (hm hu (hu.trans hv) hv)
  · rintro ht ⟨B, hB⟩
    obtain ⟨u, hu, hlarge⟩ := ((eventually_ge_atTop (0 : ℝ)).and (ht.eventually_ge_atTop (B + 1))).exists
    have := hB u hu
    linarith

variable {A X : Type*} [TopologicalSpace A] [MetricSpace X]

/-- The minimum of `G(z) + u F(x,z)` is continuous jointly in the parameter
and the nonnegative penalty coefficient. -/
theorem fiberMinimum_continuous (F : A → X → ℝ) (G : X → ℝ)
    (hF : Continuous (fun q : A × X => F q.1 q.2)) (hG : Continuous G)
    (hFn : ∀ p x, 0 ≤ F p x) (hcompact : ∀ B : ℝ, IsCompact {x | G x ≤ B}) (x₀ : X) :
    Continuous (fun q : A × Ici (0 : ℝ) => coerciveMinimumValue (F q.1) G q.2.val) := by
  let H : (A × Ici (0 : ℝ)) → X → ℝ := fun q x => G x + q.2.val * F q.1 x
  have hH : Continuous (fun q : (A × Ici (0 : ℝ)) × X => H q.1 q.2) :=
    (hG.comp continuous_snd).add
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).mul
        (hF.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)))
  exact parameterMinimumValue_continuous H G hH hG
    (fun p x => le_add_of_nonneg_right (mul_nonneg p.2.property (hFn p.1 x))) hcompact x₀

/-- An empty fiber is characterized by divergence of its monotone minimum;
this requires only continuity, nonnegativity and compact coercive sublevels. -/
theorem no_zero_iff_minimum_tendsto (F G : X → ℝ)
    (hF : Continuous F) (hG : Continuous G) (hFn : ∀ x, 0 ≤ F x) (hGn : ∀ x, 0 ≤ G x)
    (hcompact : ∀ B : ℝ, IsCompact {x | G x ≤ B}) (x₀ : X) :
    (¬∃ x : X, F x = 0) ↔ Tendsto (coerciveMinimumValue F G) atTop atTop := by
  rw [zero_iff_bounded_minimumValue F G hF hG hFn hGn hcompact x₀]
  exact monotoneOn_unbounded_iff_tendsto _
    (coerciveMinimumValue_monotoneOn F G hF hG hFn hcompact x₀)

end LeanCanny.CountingHierarchy
