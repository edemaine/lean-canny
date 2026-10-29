/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RootBranches

/-! # Equal root sets transfer properness on an open slab

The auxiliary and original equations need agree only on the retained
parameter set. Their endpoint zero sets may differ.
-/

@[expose] public section
namespace LeanCanny.Geometry.RootSlabEquivalence
open Set
variable {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
set_option backward.isDefEq.respectTransparency false

noncomputable def homeomorph (f : ℝ × E → F) (g : ℝ × E → G) (s : Set ℝ)
    (heq : ∀ t ∈ s, ∀ x, f (t, x) = 0 ↔ g (t, x) = 0) :
    (RootProjection.projection f ⁻¹' s) ≃ₜ (RootProjection.projection g ⁻¹' s) where
  toFun z := ⟨⟨z.val.val, (heq z.val.val.1 z.property z.val.val.2).mp z.val.property⟩, z.property⟩
  invFun z := ⟨⟨z.val.val, (heq z.val.val.1 z.property z.val.val.2).mpr z.val.property⟩, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

lemma proper_restriction (f : ℝ × E → F) (g : ℝ × E → G) (s : Set ℝ)
    (heq : ∀ t ∈ s, ∀ x, f (t, x) = 0 ↔ g (t, x) = 0)
    (hp : IsProperMap (s.restrictPreimage (RootProjection.projection f))) :
    IsProperMap (s.restrictPreimage (RootProjection.projection g)) := by
  let e := homeomorph f g s heq
  have H : s.restrictPreimage (RootProjection.projection g) =
      (s.restrictPreimage (RootProjection.projection f)) ∘ e.symm := rfl
  rw [H]
  exact hp.comp e.symm.isProperMap

end LeanCanny.Geometry.RootSlabEquivalence
