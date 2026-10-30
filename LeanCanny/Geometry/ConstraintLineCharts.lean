/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CoordinateLineInterval
public import LeanCanny.Geometry.RegularComponentTransport

/-! # Local product charts for one varying value of a regular constraint map

Fix every constraint except one. Restricting the full implicit-function
chart to this line supplies actual interval charts for the coarser fiber's
height projection. No global trivialization is assumed.
-/

@[expose] public section
namespace LeanCanny.Geometry.ConstraintLineCharts
open Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Fintype ι] [DecidableEq ι]

def coarseSet (f : E → ι → ℝ) (c : ι → ℝ) (r : ι) : Set E :=
  {x | ∀ j, j ≠ r → f x j = c j}

def projection (f : E → ι → ℝ) (c : ι → ℝ) (r : ι) : coarseSet f c r → ℝ :=
  fun x => f x.val r - c r

noncomputable def domainHomeomorph (f : E → ι → ℝ) (c : ι → ℝ) (r : ι) (a b : ℝ) :
    (projection f c r) ⁻¹' Ioo a b ≃ₜ f ⁻¹' CoordinateLineInterval.region c r a b where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem exists_charts (f : E → ι → ℝ) (c : ι → ℝ) (r : ι) (a b : ℝ)
    (hf : ∀ x, f x ∈ CoordinateLineInterval.region c r a b → ContDiffAt ℝ 1 f x)
    (hregular : ∀ x, f x ∈ CoordinateLineInterval.region c r a b →
      Function.Surjective (fderiv ℝ f x)) :
    ∃ chart : ∀ x : (projection f c r) ⁻¹' Ioo a b,
      OpenPartialHomeomorph ((projection f c r) ⁻¹' Ioo a b) (Ioo a b × (fderiv ℝ f x.val.val).ker),
      (∀ x, x ∈ (chart x).source) ∧
      ∀ z x, x ∈ (chart z).source → (chart z x).1 = (Ioo a b).restrictPreimage (projection f c r) x := by
  obtain ⟨C, HC, HF⟩ := RegularComponentTransport.exists_charts f (CoordinateLineInterval.region c r a b) hf hregular
  let e := domainHomeomorph f c r a b
  let base := (CoordinateLineInterval.homeomorph c r a b).symm
  let chart (x : (projection f c r) ⁻¹' Ioo a b) :=
    (e.toOpenPartialHomeomorph.trans (C (e x))).trans
      (base.prodCongr (Homeomorph.refl (↥(fderiv ℝ f x.val.val).ker))).toOpenPartialHomeomorph
  refine ⟨chart, ?_, ?_⟩
  · intro x
    change x ∈ (e.toOpenPartialHomeomorph.trans (C (e x))).source ∧ _
    exact ⟨⟨mem_univ x, HC (e x)⟩, mem_univ _⟩
  · intro z x hx
    have HM : e x ∈ (C (e z)).source := hx.1.2
    have HE := congrArg base (HF (e z) (e x) HM)
    apply Subtype.ext
    exact congrArg Subtype.val HE

end LeanCanny.Geometry.ConstraintLineCharts
