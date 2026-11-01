/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Homeomorph.Lemmas
/-! # A single reciprocal equation is a unique continuous graph above a positive margin -/
@[expose] public section
namespace LeanCanny.Geometry.PositiveReciprocalGraph
open Set
variable {X : Type*} [TopologicalSpace X]

abbrev Space (r : X → ℝ) := {z : X × ℝ // z.2*r z.1=1}
abbrev Base (r : X → ℝ) := {x : X // 0<r x}

noncomputable def homeomorph (r : X → ℝ) (hr : Continuous r) (hn : ∀ x,0≤r x) : Space r ≃ₜ Base r where
  toFun z := ⟨z.val.1,lt_of_le_of_ne (hn z.val.1) (by
    intro H
    have HE:=z.property
    rw [← H,mul_zero] at HE
    exact zero_ne_one HE)⟩
  invFun x := ⟨(x.val,(r x.val)⁻¹),inv_mul_cancel₀ x.property.ne'⟩
  left_inv z := by
    apply Subtype.ext
    change (z.val.1,(r z.val.1)⁻¹)=z.val
    apply Prod.ext
    · rfl
    · have H : r z.val.1≠0 := by
        intro H
        have HE:=z.property
        rw [H,mul_zero] at HE
        exact zero_ne_one HE
      simpa only [one_div] using ((eq_div_iff H).mpr z.property).symm
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.prodMk
    ((hr.comp continuous_subtype_val).inv₀ (fun x => x.property.ne'))).subtype_mk _

end LeanCanny.Geometry.PositiveReciprocalGraph
