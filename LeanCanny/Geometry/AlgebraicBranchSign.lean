/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.AlgebraicBranchZero
public import Mathlib.Topology.Order.IntermediateValue

/-! # Constant signs along retained algebraic branches

The same trailing-coefficient exclusion that makes a zero test constant also
makes both strict signs constant. This includes tests vanishing identically
on a branch. Continuous disjoint scalar branches retain their root order.
-/

@[expose] public section
namespace LeanCanny.Geometry.AlgebraicBranchSign
open Set
variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]

theorem sign_iff_of_zero_iff (f : X → ℝ) (hf : Continuous f)
    (hz : ∀ x y, f x = 0 ↔ f y = 0) (x y : X) :
    (f x < 0 ↔ f y < 0) ∧ (0 < f x ↔ 0 < f y) := by
  have hneg (a b : X) (ha : f a < 0) : f b < 0 := by
    by_contra hb
    obtain ⟨c, hc⟩ := intermediate_value_univ₂ hf continuous_const ha.le (le_of_not_gt hb)
    have he := (hz c a).mp hc
    linarith
  have hpos (a b : X) (ha : 0 < f a) : 0 < f b := by
    by_contra hb
    obtain ⟨c, hc⟩ := intermediate_value_univ₂ continuous_const hf ha.le (le_of_not_gt hb)
    have he := (hz c a).mp hc.symm
    linarith
  exact ⟨⟨hneg x y, hneg y x⟩, ⟨hpos x y, hpos y x⟩⟩

theorem sign_iff (p : Polynomial (Polynomial ℝ)) (r f : X → ℝ)
    (hr : Continuous r) (hf : Continuous f)
    (hroot : ∀ x, p.eval₂ (Polynomial.evalRingHom (r x)) (f x) = 0)
    (htrail : ∀ x, p.trailingCoeff.eval (r x) ≠ 0) (x y : X) :
    (f x < 0 ↔ f y < 0) ∧ (0 < f x ↔ 0 < f y) :=
  sign_iff_of_zero_iff f hf (AlgebraicBranchZero.zero_iff p r f hr hf hroot htrail) x y

/-- An anchored ordinal of a disjoint scalar root branch remains in the
same relative order throughout the connected parameter space. -/
theorem order_iff (f g : X → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hne : ∀ x, f x ≠ g x) (x y : X) : f x < g x ↔ f y < g y := by
  have hz (a b : X) : f a - g a = 0 ↔ f b - g b = 0 := by
    simp only [sub_eq_zero, hne, iff_self]
  simpa only [sub_neg] using (sign_iff_of_zero_iff (fun t => f t - g t) (hf.sub hg) hz x y).1

end LeanCanny.Geometry.AlgebraicBranchSign
