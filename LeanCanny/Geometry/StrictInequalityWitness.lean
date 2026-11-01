/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CircularWitness
public import Mathlib.Analysis.Real.Sqrt
/-! # A strict inequality has an algebraic lift with connected circular fibers

The equation f(x)*(u²+v²)=1 has precisely f(x)>0 as its projection.
Every witness over a point lies on one circle. This preserves paths between
ANY chosen endpoint witnesses and preserves whole-space connectedness,
without compactness or boundedness assumptions on the original set.
-/
@[expose] public section
namespace LeanCanny.Geometry.StrictInequalityWitness
open Set CircularWitness
open scoped Classical
variable {X : Type*} [TopologicalSpace X]

def positive (f : X → ℝ) : Set X := {x | 0 < f x}
def equation (f : X → ℝ) : Set (X × Plane) := {z | f z.1 * ‖z.2‖^2 = 1}

noncomputable def radius (f : X → ℝ) (x : positive f) : ℝ := (Real.sqrt (f x.val))⁻¹

theorem norm_iff (a : ℝ) (w : Plane) :
    a * ‖w‖^2 = 1 ↔ 0 < a ∧ ‖w‖ = (Real.sqrt a)⁻¹ := by
  constructor
  · intro H
    have HA : 0 < a := by nlinarith [sq_nonneg ‖w‖]
    refine ⟨HA,?_⟩
    apply (sq_eq_sq₀ (norm_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _))).mp
    rw [inv_pow,Real.sq_sqrt HA.le]
    exact eq_inv_of_mul_eq_one_left (by nlinarith : ‖w‖^2*a=1)
  · rintro ⟨HA,HW⟩
    rw [HW,inv_pow,Real.sq_sqrt HA.le,mul_inv_cancel₀ (ne_of_gt HA)]

noncomputable def homeomorph (f : X → ℝ) : equation f ≃ₜ CircularWitness.Space (radius f) where
  toFun z := ⟨(⟨z.val.1,((norm_iff _ _).mp z.property).1⟩,z.val.2),((norm_iff _ _).mp z.property).2⟩
  invFun z := ⟨(z.val.1.val,z.val.2),(norm_iff _ _).mpr ⟨z.val.1.property,z.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)

omit [TopologicalSpace X] in
theorem radius_nonneg (f : X → ℝ) (x : positive f) : 0 ≤ radius f x := inv_nonneg.mpr (Real.sqrt_nonneg _)

theorem continuous_radius (f : X → ℝ) (hf : Continuous f) : Continuous (radius f) :=
  ((hf.comp continuous_subtype_val).sqrt).inv₀ (fun x => ne_of_gt (Real.sqrt_pos.mpr x.property))

def projection (f : X → ℝ) (z : equation f) : positive f :=
  ⟨z.val.1,((norm_iff _ _).mp z.property).1⟩

theorem joined_iff (f : X → ℝ) (hf : Continuous f) (y z : equation f) :
    JoinedIn univ y z ↔ JoinedIn univ (projection f y) (projection f z) := by
  have HE : JoinedIn univ y z ↔ JoinedIn univ (homeomorph f y) (homeomorph f z) := by
    constructor
    · intro H
      exact (H.map (homeomorph f).continuous.continuousOn).mono (subset_univ _)
    · intro H
      simpa only [Homeomorph.symm_apply_apply] using
        (H.map (homeomorph f).symm.continuous.continuousOn).mono (subset_univ _)
  exact HE.trans (CircularWitness.joined_iff (radius f) (radius_nonneg f) (continuous_radius f hf) _ _)

theorem preconnected_iff (f : X → ℝ) (hf : Continuous f) :
    IsPreconnected (equation f) ↔ IsPreconnected (positive f) := by
  rw [isPreconnected_iff_preconnectedSpace,isPreconnected_iff_preconnectedSpace,
    preconnectedSpace_iff_univ,preconnectedSpace_iff_univ]
  have HE : IsPreconnected (univ : Set (equation f)) ↔
      IsPreconnected (univ : Set (CircularWitness.Space (radius f))) := by
    constructor
    · intro H
      simpa only [Set.image_univ_of_surjective (homeomorph f).surjective] using H.image (homeomorph f) (homeomorph f).continuous.continuousOn
    · intro H
      simpa only [Set.image_univ_of_surjective (homeomorph f).symm.surjective] using H.image (homeomorph f).symm (homeomorph f).symm.continuous.continuousOn
  exact HE.trans (CircularWitness.preconnected_iff (radius f) (radius_nonneg f) (continuous_radius f hf))

end LeanCanny.Geometry.StrictInequalityWitness
