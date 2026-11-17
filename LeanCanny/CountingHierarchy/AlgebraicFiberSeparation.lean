/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.AlgebraicPowerScaleTest
public import LeanCanny.CountingHierarchy.DegreePieceSeparation
public import LeanCanny.CountingHierarchy.FiberCoerciveMinimum

/-! # Empty fibers are relatively clopen on algebraic degree pieces -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Polynomial Filter Set
open scoped Topology Classical

variable {A X : Type*} [TopologicalSpace A] [MetricSpace X]

/-- The analytic separation theorem for the two-block construction. `P` is
the parameter-first critical-value polynomial, and `E` its fixed-power section.
The parameter space can be any fixed-degree-piece subtype. -/
theorem emptyFibers_isClopen_on_degree_piece (F : A → X → ℝ) (G : X → ℝ)
    (hF : Continuous (fun q : A × X => F q.1 q.2)) (hG : Continuous G)
    (hFn : ∀ p x, 0 ≤ F p x) (hGn : ∀ x, 0 ≤ G x)
    (hcompact : ∀ B : ℝ, IsCompact {x | G x ≤ B}) (x₀ : X)
    (D : ℕ) (P : A → Polynomial (Polynomial ℝ)) (hP : ∀ x, P x ≠ 0)
    (hPdegree : ∀ x j, ((P x).coeff j).natDegree ≤ D)
    (hroot : ∀ x u, 0 ≤ u → (P x).eval₂
      (Polynomial.evalRingHom (coerciveMinimumValue (F x) G u)) u = 0)
    (E : A → Polynomial ℝ) (d : ℕ)
    (hcoeff : ∀ i, Continuous (fun x => (E x).coeff i))
    (hdegree : ∀ x, (E x).natDegree ≤ d) (hlead : ∀ x, (E x).coeff d ≠ 0)
    (hsection : ∀ x v, (E x).eval v = (P x).eval₂ (Polynomial.evalRingHom v) (v ^ (D + 1))) :
    IsClopen {x | ¬∃ z : X, F x z = 0} := by
  let m := fun x => coerciveMinimumValue (F x) G
  have hFx (x : A) : Continuous (F x) := hF.comp (continuous_const.prodMk continuous_id)
  have hmn (x : A) (u : ℝ) (hu : 0 ≤ u) : 0 ≤ m x u := by
    obtain ⟨z, hz⟩ := exists_minimizer_of_compact_sublevels (F x) G (hFx x) hG (hFn x) hcompact x₀ u hu
    rw [show m x u = G z + u * F x z from coerciveMinimumValue_eq_of_minimizer _ _ u z hz]
    exact add_nonneg (hGn z) (mul_nonneg hu (hFn x z))
  let f := fun x v => m x ((max v 0) ^ (D + 1)) - v
  have hf : Continuous (fun q : A × ℝ => f q.1 q.2) := by
    have hp : Continuous (fun q : A × ℝ => (max q.2 0) ^ (D + 1)) :=
      (continuous_snd.max continuous_const).pow _
    have hm := fiberMinimum_continuous F G hF hG hFn hcompact x₀
    have hmap : Continuous (fun q : A × ℝ => (q.1,
        (⟨(max q.2 0) ^ (D + 1), pow_nonneg (le_max_right _ _) _⟩ : Ici (0 : ℝ)))) :=
      continuous_fst.prodMk (hp.subtype_mk _)
    exact (hm.comp hmap).sub continuous_snd
  apply eventualSign_isClopen_on_degree_piece E d hcoeff hdegree hlead f hf
  · intro x v hv
    have hvpos : 0 ≤ v := by
      have hn := hmn x ((max v 0) ^ (D + 1)) (pow_nonneg (le_max_right _ _) _)
      dsimp only [f] at hv
      linarith
    have hmval : m x (v ^ (D + 1)) = v := by
      simpa only [f, max_eq_left hvpos, sub_eq_zero] using hv
    rw [hsection]
    have hr : (P x).eval₂ (Polynomial.evalRingHom (m x (v ^ (D + 1)))) (v ^ (D + 1)) = 0 :=
      hroot x _ (pow_nonneg hvpos _)
    rw [hmval] at hr
    exact hr
  · intro x hx
    have hdiv := (no_zero_iff_minimum_tendsto (F x) G (hFx x) hG (hFn x) hGn hcompact x₀).mp hx
    have htest := divergent_algebraic_branch_power_gt (P x) (hP x) D (hPdegree x) (m x) hdiv
      (hmn x) (fun u hu => hroot x u hu.le)
    filter_upwards [htest, eventually_ge_atTop (0 : ℝ)] with v hv hvpos
    simpa only [f, max_eq_left hvpos, sub_pos] using hv
  · intro x hx
    have hz : ∃ z : X, F x z = 0 := not_not.mp hx
    have hb := (zero_iff_bounded_minimumValue (F x) G (hFx x) hG (hFn x) hGn hcompact x₀).mp hz
    have htest := bounded_branch_power_lt D (m x) hb
    filter_upwards [htest, eventually_ge_atTop (0 : ℝ)] with v hv hvpos
    simpa only [f, max_eq_left hvpos, sub_neg] using hv

end LeanCanny.CountingHierarchy
