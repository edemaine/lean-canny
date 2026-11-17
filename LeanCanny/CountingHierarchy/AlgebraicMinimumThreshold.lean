/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PolynomialBranchLimit
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Order.IntermediateValue

/-! # Threshold tests for monotone algebraic branches -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial Filter Set
open scoped Topology

/-- A nondecreasing function on the nonnegative half line has a finite
 upper limiting value whenever it is bounded above there. -/
theorem monotoneOn_exists_upper_limit (m : ℝ → ℝ) (hm : MonotoneOn m (Ici 0))
    (hb : ∃ B, ∀ u, 0 ≤ u → m u ≤ B) :
    ∃ L, Tendsto m atTop (𝓝 L) ∧ ∀ u, 0 ≤ u → m u ≤ L := by
  let f : ℝ → ℝ := fun u => m (max u 0)
  have hf : Monotone f := fun u v huv =>
    hm (le_max_right u 0) (le_max_right v 0) (max_le_max huv le_rfl)
  have hb' : BddAbove (range f) := by
    obtain ⟨B, hB⟩ := hb
    exact ⟨B, by rintro _ ⟨u, rfl⟩; exact hB _ (le_max_right _ _)⟩
  refine ⟨⨆ u, f u, ?_, ?_⟩
  · apply (tendsto_atTop_ciSup hf hb').congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact congrArg m (max_eq_left hu)
  · intro u hu
    simpa only [f, max_eq_left hu] using (le_ciSup hb' u)

/-- All values of a bounded monotone root branch lie below any threshold
 exceeding the coefficient-mass bound for its finite limiting value. -/
theorem bounded_branch_lt_threshold (P : Polynomial (Polynomial ℤ)) (hP : P ≠ 0)
    (m : ℝ → ℝ) (hm : MonotoneOn m (Ici 0))
    (hroot : ∀ u : ℝ, 0 < u →
      P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) (m u)) u = 0)
    (R : ℝ) (hR : (LeanCanny.Algebra.coefficientMass P.leadingCoeff : ℝ) + 1 ≤ R)
    (hb : ∃ B, ∀ u, 0 ≤ u → m u ≤ B) :
    ∀ u, 0 ≤ u → m u < R := by
  obtain ⟨L, hL, hle⟩ := monotoneOn_exists_upper_limit m hm hb
  have hbound := abs_branch_limit_lt P hP m L hL hroot
  intro u hu
  exact (hle u hu).trans_lt ((le_abs_self L).trans_lt (hbound.trans_le hR))

/-- A continuous monotone branch cannot cross a level which is avoided
 by its defining polynomial throughout the tail. -/
theorem bounded_of_no_threshold_crossing (m : ℝ → ℝ)
    (hm : MonotoneOn m (Ici 0)) (hc : ContinuousOn m (Ici 0))
    (U R : ℝ) (hU : 0 ≤ U) (hstart : m U < R)
    (havoid : ∀ u, U ≤ u → m u ≠ R) :
    ∀ u, 0 ≤ u → m u ≤ R := by
  intro u hu
  by_cases hle : u ≤ U
  · exact (hm hu hU hle).trans hstart.le
  · have hUu : U ≤ u := (le_of_not_ge hle)
    by_contra hnot
    have hRu : R ≤ m u := (le_of_lt (lt_of_not_ge hnot))
    obtain ⟨v, hv, he⟩ := intermediate_value_Icc hUu
      (hc.mono (fun x hx => hU.trans hx.1)) ⟨hstart.le, hRu⟩
    exact havoid v hv.1 he

end LeanCanny.CountingHierarchy
