/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.WeakBooleanWitness
/-! # Continuous attenuated circular witnesses for a finite union of strict inequalities

A simplex weight activates each strict atom through fᵢ‖wᵢ‖²=λᵢ².
The canonical weight max(fᵢ,0)/Σmax(fⱼ,0) and circle coordinate
√max(fᵢ,0)/Σmax(fⱼ,0) remain continuous when an individual atom ceases
to hold. Only the positive union margin occurs in a denominator.
-/
@[expose] public section
namespace LeanCanny.Geometry.OpenUnionCircleWitness
open Set CircularWitness
open scoped BigOperators Classical
variable {X I : Type*} [Fintype I]

abbrev Base (f : I → X → ℝ) := {x : X // ∃ i, 0<f i x}
abbrev Space (f : I → X → ℝ) := {z : X × ((I → ℝ) × (I → Plane)) //
  (∀ i, 0≤z.2.1 i) ∧ (∑ i, z.2.1 i)=1 ∧ ∀ i, f i z.1*‖z.2.2 i‖^2=(z.2.1 i)^2}

noncomputable def margin (f : I → X → ℝ) (x : X) : ℝ := ∑ i, max (f i x) 0

theorem margin_pos (f : I → X → ℝ) (x : Base f) : 0<margin f x.val := by
  obtain ⟨i,hi⟩ := x.property
  apply lt_of_lt_of_le (hi.trans_le (le_max_left _ _))
  exact Finset.single_le_sum (f := fun j => max (f j x.val) 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ i)

def projection (f : I → X → ℝ) (z : Space f) : Base f := by
  refine ⟨z.val.1,?_⟩
  by_contra H
  push Not at H
  have Hzero : ∀ i, z.val.2.1 i=0 := by
    intro i
    have HE := z.property.2.2 i
    have HF := H i
    have HW := sq_nonneg ‖z.val.2.2 i‖
    have HL := z.property.1 i
    have HP : f i z.val.1*‖z.val.2.2 i‖^2≤0 := mul_nonpos_of_nonpos_of_nonneg HF HW
    nlinarith [sq_nonneg (z.val.2.1 i)]
  have HS := z.property.2.1
  simp only [Hzero,Finset.sum_const_zero] at HS
  norm_num at HS

noncomputable def weight (f : I → X → ℝ) (x : Base f) (i : I) : ℝ := max (f i x.val) 0/margin f x.val
noncomputable def circle (f : I → X → ℝ) (x : Base f) (i : I) : Plane :=
  (Real.sqrt (max (f i x.val) 0)/margin f x.val) • unit

theorem weight_nonneg (f : I → X → ℝ) (x : Base f) (i : I) : 0≤weight f x i :=
  div_nonneg (le_max_right _ _) (margin_pos f x).le

theorem weight_sum (f : I → X → ℝ) (x : Base f) : (∑ i,weight f x i)=1 := by
  simp only [weight,← Finset.sum_div]
  exact div_self (margin_pos f x).ne'

theorem max_identity (a : ℝ) : a*max a 0=(max a 0)^2 := by
  by_cases H : 0≤a
  · rw [max_eq_left H,pow_two]
  · rw [max_eq_right (le_of_lt (lt_of_not_ge H))]
    norm_num

theorem circle_equation (f : I → X → ℝ) (x : Base f) (i : I) :
    f i x.val*‖circle f x i‖^2=(weight f x i)^2 := by
  simp only [circle,weight,norm_smul,unit_norm,mul_one,Real.norm_eq_abs,sq_abs,div_pow,
    Real.sq_sqrt (le_max_right (f i x.val) 0),← mul_div_assoc,max_identity]

noncomputable def centerSection (f : I → X → ℝ) (x : Base f) : Space f :=
  ⟨(x.val,(weight f x,circle f x)),weight_nonneg f x,weight_sum f x,circle_equation f x⟩

theorem projection_section (f : I → X → ℝ) (x : Base f) : projection f (centerSection f x)=x := rfl

theorem continuous_projection [TopologicalSpace X] (f : I → X → ℝ) : Continuous (projection f) :=
  (continuous_fst.comp continuous_subtype_val).subtype_mk _

theorem continuous_section [TopologicalSpace X] (f : I → X → ℝ) (hf : ∀ i, Continuous (f i)) : Continuous (centerSection f) := by
  have HM : Continuous (fun x : Base f => margin f x.val) :=
    continuous_finsetSum Finset.univ (fun i _ => ((hf i).comp continuous_subtype_val).max continuous_const)
  have HW : Continuous (fun x : Base f => weight f x) := continuous_pi (fun i =>
    (((hf i).comp continuous_subtype_val).max continuous_const).div HM (fun x => (margin_pos f x).ne'))
  have HC : Continuous (fun x : Base f => circle f x) := continuous_pi (fun i =>
    ((((hf i).comp continuous_subtype_val).max continuous_const).sqrt.div HM (fun x => (margin_pos f x).ne')).smul continuous_const)
  exact (continuous_subtype_val.prodMk (HW.prodMk HC)).subtype_mk _

end LeanCanny.Geometry.OpenUnionCircleWitness
