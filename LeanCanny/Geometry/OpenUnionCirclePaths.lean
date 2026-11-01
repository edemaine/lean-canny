/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.OpenUnionCircleWitness
public import LeanCanny.Geometry.ScaledCirclePaths
/-! # Connected fibers of the attenuated finite strict-union witness -/
@[expose] public section
namespace LeanCanny.Geometry.OpenUnionCircleWitness
open Set CircularWitness
open scoped BigOperators Classical
variable {X I : Type*} [Fintype I]

noncomputable def normalized (f : I → X → ℝ) (z : Space f) : Space f :=
  ⟨(z.val.1,(z.val.2.1,fun i => ScaledCirclePaths.center (f i z.val.1) (z.val.2.1 i))),
    z.property.1,z.property.2.1,fun i => ScaledCirclePaths.center_equation _ _
      (ScaledCirclePaths.inactive (z.property.1 i) (z.property.2.2 i))⟩

theorem center_weight (f : I → X → ℝ) (x : Base f) (i : I) :
    ScaledCirclePaths.center (f i x.val) (weight f x i)=circle f x i := by
  by_cases H : 0<f i x.val
  · rw [ScaledCirclePaths.center,ite_eq_left H]
    unfold circle weight
    rw [max_eq_left H.le]
    apply congrArg (fun a : ℝ => a • unit)
    have HS := Real.sq_sqrt H.le
    have HD := (margin_pos f x).ne'
    have HR := (Real.sqrt_pos.mpr H).ne'
    field_simp
    nlinarith
  · rw [ScaledCirclePaths.center,ite_eq_right H]
    simp only [circle,max_eq_right (le_of_not_gt H),Real.sqrt_zero,zero_div,zero_smul]

theorem joined_normalized [TopologicalSpace X] (f : I → X → ℝ) (z : Space f) :
    JoinedIn univ z (normalized f z) := by
  choose γ Hγ using fun i => ScaledCirclePaths.atom_path (f i z.val.1) (z.val.2.1 i) (z.val.2.2 i)
    (z.property.1 i) (z.property.2.2 i)
  let P : Path z (normalized f z) :=
    { toFun := fun t => ⟨(z.val.1,(z.val.2.1,fun i => γ i t)),z.property.1,z.property.2.1,fun i => Hγ i t⟩
      continuous_toFun := (continuous_const.prodMk (continuous_const.prodMk
        (continuous_pi (fun i => (γ i).continuous)))).subtype_mk _
      source' := by
        apply Subtype.ext
        change (z.val.1,(z.val.2.1,fun i => γ i 0))=z.val
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · funext i; exact (γ i).source
      target' := by
        apply Subtype.ext
        change (z.val.1,(z.val.2.1,fun i => γ i 1))=(z.val.1,(z.val.2.1,fun i => ScaledCirclePaths.center (f i z.val.1) (z.val.2.1 i)))
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · funext i; exact (γ i).target }
  exact ⟨P,fun _ => mem_univ _⟩

noncomputable def blend (f : I → X → ℝ) (z : Space f) (t : ℝ) (i : I) : ℝ :=
  (1-t)*z.val.2.1 i+t*weight f (projection f z) i

theorem blend_nonneg (f : I → X → ℝ) (z : Space f) {t : ℝ} (ht : 0≤t) (ht1 : t≤1) (i : I) :
    0≤blend f z t i := add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (z.property.1 i))
      (mul_nonneg ht (weight_nonneg f _ i))

theorem blend_sum (f : I → X → ℝ) (z : Space f) (t : ℝ) : (∑ i,blend f z t i)=1 := by
  simp only [blend,Finset.sum_add_distrib,← Finset.mul_sum,z.property.2.1,weight_sum,mul_one]
  ring

theorem blend_inactive (f : I → X → ℝ) (z : Space f) (t : ℝ) (i : I) (hi : f i z.val.1≤0) :
    blend f z t i=0 := by
  have HZ := ScaledCirclePaths.inactive (z.property.1 i) (z.property.2.2 i) hi
  have HW : weight f (projection f z) i=0 := by
    unfold weight
    change max (f i z.val.1) 0/margin f z.val.1=0
    rw [max_eq_right hi,zero_div]
  simp only [blend,HZ,HW,mul_zero,add_zero]

theorem blend_zero (f : I → X → ℝ) (z : Space f) : blend f z 0=z.val.2.1 := by
  funext i
  simp only [blend,sub_zero,one_mul,zero_mul,add_zero]

theorem blend_one (f : I → X → ℝ) (z : Space f) : blend f z 1=weight f (projection f z) := by
  funext i
  simp only [blend,sub_self,zero_mul,one_mul,zero_add]

noncomputable def moving (f : I → X → ℝ) (z : Space f) (t : unitInterval) : Space f :=
  ⟨(z.val.1,(blend f z t,fun i => ScaledCirclePaths.center (f i z.val.1) (blend f z t i))),
    blend_nonneg f z t.property.1 t.property.2,blend_sum f z t,
    fun i => ScaledCirclePaths.center_equation _ _ (blend_inactive f z t i)⟩

theorem joined_section [TopologicalSpace X] (f : I → X → ℝ) (z : Space f) :
    JoinedIn univ (normalized f z) (centerSection f (projection f z)) := by
  have HB : Continuous (fun t : unitInterval => blend f z t) := by
    apply continuous_pi
    intro i
    exact ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)
  have HC : Continuous (fun t : unitInterval => fun i => ScaledCirclePaths.center (f i z.val.1) (blend f z t i)) :=
    continuous_pi (fun i => (ScaledCirclePaths.continuous_center _).comp ((continuous_apply i).comp HB))
  let P : Path (normalized f z) (centerSection f (projection f z)) :=
    { toFun := moving f z
      continuous_toFun := (continuous_const.prodMk (HB.prodMk HC)).subtype_mk _
      source' := by
        apply Subtype.ext
        have H0 : ((0 : unitInterval) : ℝ)=0 := rfl
        simp only [moving,H0,blend_zero]
        rfl
      target' := by
        apply Subtype.ext
        have H1 : ((1 : unitInterval) : ℝ)=1 := rfl
        simp only [moving,H1,blend_one]
        change (z.val.1,(weight f (projection f z),fun i => ScaledCirclePaths.center (f i z.val.1) (weight f (projection f z) i)))=
          (z.val.1,(weight f (projection f z),circle f (projection f z)))
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · rfl
          · funext i; exact center_weight f (projection f z) i }
  exact ⟨P,fun _ => mem_univ _⟩

theorem fiber_joined [TopologicalSpace X] (f : I → X → ℝ) (z : Space f) :
    JoinedIn univ z (centerSection f (projection f z)) :=
  (joined_normalized f z).trans (joined_section f z)

theorem joined_iff [TopologicalSpace X] (f : I → X → ℝ) (hf : ∀ i, Continuous (f i)) (y z : Space f) :
    JoinedIn univ y z ↔ JoinedIn univ (projection f y) (projection f z) :=
  ConnectedWitnessProjection.joined_iff (projection f) (centerSection f)
    (continuous_projection f) (continuous_section f hf) (fiber_joined f) y z

theorem preconnected_iff [TopologicalSpace X] (f : I → X → ℝ) (hf : ∀ i, Continuous (f i)) :
    IsPreconnected (univ : Set (Space f)) ↔ IsPreconnected (univ : Set (Base f)) :=
  ConnectedWitnessProjection.preconnected_iff (projection f) (centerSection f)
    (continuous_projection f) (continuous_section f hf) (projection_section f) (fiber_joined f)

end LeanCanny.Geometry.OpenUnionCircleWitness
