/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.LocalProductFibers
public import Mathlib.Topology.LocalAtTarget

/-! # Restricting local product charts to a parameter region

Local product coordinates pull back to any subset of the parameter space.
Thus a regular-value region can be used as the base of component transport
even when the original map has critical values elsewhere.
-/

@[expose] public section

namespace LeanCanny.Geometry.LocalProductFibers
open Set Topology

variable {X B G : Type*} [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace G]

/-- Pull a product chart back along inclusion of a parameter region. The base
subset need not be open. Every source and target used below is relatively open. -/
theorem exists_restricted_chart (p : X → B) (S : Set B)
    (e : OpenPartialHomeomorph X (B × G)) (a : p ⁻¹' S) (ha : a.val ∈ e.source)
    (hfirst : ∀ x ∈ e.source, (e x).1 = p x) :
    ∃ chart : OpenPartialHomeomorph (p ⁻¹' S) (S × G), a ∈ chart.source ∧
      ∀ x ∈ chart.source, (chart x).1 = S.restrictPreimage p x := by
  classical
  let U : Set (p ⁻¹' S) := Subtype.val ⁻¹' e.source
  let forget : S × G → B × G := fun y => (y.1.val, y.2)
  let V : Set (S × G) := forget ⁻¹' e.target
  have hU : IsOpen U := e.open_source.preimage continuous_subtype_val
  have hforget : Continuous forget :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hV : IsOpen V := e.open_target.preimage hforget
  have hmem (x : U) : (e x.val.val).1 ∈ S := by
    rw [hfirst x.val.val x.property]
    exact x.val.property
  have hinvmem (y : V) : p (e.symm (forget y.val)) ∈ S := by
    have he := (hfirst _ (e.map_target y.property)).symm.trans (congrArg Prod.fst (e.right_inv y.property))
    rw [he]
    exact y.val.1.property
  let H : U ≃ₜ V := {
    toFun := fun x => ⟨(⟨(e x.val.val).1, hmem x⟩, (e x.val.val).2), e.map_source x.property⟩
    invFun := fun y => ⟨⟨e.symm (forget y.val), hinvmem y⟩, e.map_target y.property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      exact e.left_inv x.property
    right_inv := by
      intro y
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst (e.right_inv y.property)
      · exact congrArg (fun z : B × G => z.2) (e.right_inv y.property)
    continuous_toFun := by
      have he : Continuous (fun x : U => e x.val.val) :=
        e.continuousOn.comp_continuous (continuous_subtype_val.comp continuous_subtype_val)
          (fun x => x.property)
      exact (((continuous_fst.comp he).subtype_mk _).prodMk (continuous_snd.comp he)).subtype_mk _
    continuous_invFun := by
      have he : Continuous (fun y : V => e.symm (forget y.val)) :=
        e.symm.continuousOn.comp_continuous (hforget.comp continuous_subtype_val)
          (fun y => y.property)
      exact (he.subtype_mk _).subtype_mk _ }
  let : Nonempty U := ⟨⟨a, ha⟩⟩
  let : Nonempty V := ⟨H ⟨a, ha⟩⟩
  let incU := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : U → (p ⁻¹' S))
  let incV := hV.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : V → (S × G))
  let chart := (incU.symm.trans H.toOpenPartialHomeomorph).trans incV
  have hsource : chart.source = U := by
    simp only [chart, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      preimage_univ, inter_univ, OpenPartialHomeomorph.symm_source, incU, incV,
      IsOpenEmbedding.toOpenPartialHomeomorph_source, IsOpenEmbedding.toOpenPartialHomeomorph_target,
      Subtype.range_val]
  refine ⟨chart, hsource ▸ ha, ?_⟩
  intro x hx
  have hxU : x ∈ U := hsource ▸ hx
  have hxinc : x ∈ incU.target := by
    simpa only [incU, IsOpenEmbedding.toOpenPartialHomeomorph_target, Subtype.range_val] using hxU
  have hinc : (incU.symm x).val = x := incU.right_inv hxinc
  apply Subtype.ext
  change (e (incU.symm x).val.val).1 = p x.val
  exact (hfirst _ (incU.symm x).property).trans (congrArg (fun w : p ⁻¹' S => p w.val) hinc)

section Homeomorphs
variable {Y C : Type*} [TopologicalSpace Y] [TopologicalSpace C]
  {H : Y → Type*} [∀ y, TopologicalSpace (H y)]

/-- Change source and base coordinates in a point-dependent product atlas. -/
theorem exists_transported_charts (p : X → B) (q : Y → C)
    (source : X ≃ₜ Y) (base : B ≃ₜ C)
    (chart : ∀ y, OpenPartialHomeomorph Y (C × H y))
    (hsource : ∀ y, y ∈ (chart y).source)
    (hfirst : ∀ a y, y ∈ (chart a).source → (chart a y).1 = q y)
    (hmap : ∀ x, base.symm (q (source x)) = p x) :
    ∃ atlas : ∀ x, OpenPartialHomeomorph X (B × H (source x)),
      (∀ x, x ∈ (atlas x).source) ∧
        ∀ a x, x ∈ (atlas a).source → (atlas a x).1 = p x := by
  let atlas := fun x => (source.toOpenPartialHomeomorph.trans (chart (source x))).trans
    ((base.symm.prodCongr (Homeomorph.refl (H (source x)))).toOpenPartialHomeomorph)
  have hmem (a x : X) : x ∈ (atlas a).source ↔ source x ∈ (chart (source a)).source := by
    simp only [atlas, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      preimage_univ, inter_univ, mem_inter_iff, mem_univ, true_and]
    rfl
  refine ⟨atlas, (fun x => (hmem x x).mpr (hsource (source x))), ?_⟩
  intro a x hx
  change base.symm (chart (source a) (source x)).1 = p x
  rw [hfirst _ _ ((hmem a x).mp hx)]
  exact hmap x

end Homeomorphs
end LeanCanny.Geometry.LocalProductFibers
