/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Homeomorph.Defs

/-! # Varying one constraint value is homeomorphic to a real interval -/

@[expose] public section
namespace LeanCanny.Geometry.CoordinateLineInterval
open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [DecidableEq ι]

def region (c : ι → ℝ) (r : ι) (a b : ℝ) : Set (ι → ℝ) :=
  {y | (∀ j, j ≠ r → y j = c j) ∧ y r - c r ∈ Ioo a b}

def value (c : ι → ℝ) (r : ι) (t : ℝ) : ι → ℝ := fun j => if j = r then c r + t else c j

noncomputable def homeomorph (c : ι → ℝ) (r : ι) (a b : ℝ) : Ioo a b ≃ₜ region c r a b where
  toFun t := ⟨value c r t.val, ⟨fun j hj => by simp only [value, ite_eq_right hj], by
    simpa only [value, ite_true, add_sub_cancel_left] using t.property⟩⟩
  invFun y := ⟨y.val r - c r, y.property.2⟩
  left_inv t := by
    apply Subtype.ext
    simp only [value, ite_true, add_sub_cancel_left]
  right_inv y := by
    apply Subtype.ext
    funext j
    by_cases hj : j = r
    · subst j
      simp only [value, ite_true]
      ring
    · simp only [value, ite_eq_right hj]
      exact (y.property.1 j hj).symm
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    by_cases hj : j = r
    · simp only [value, ite_eq_left hj]
      exact continuous_const.add continuous_subtype_val
    · simp only [value, ite_eq_right hj]
      exact continuous_const
  continuous_invFun := (((continuous_apply r).comp continuous_subtype_val).sub continuous_const).subtype_mk _

end LeanCanny.Geometry.CoordinateLineInterval
