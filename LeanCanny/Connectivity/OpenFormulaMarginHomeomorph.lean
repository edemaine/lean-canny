/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.OpenFormulaMarginRoot
/-! # The actual closed margin source is homeomorphic to the original strict-positive formula -/
@[expose] public section
namespace LeanCanny.Connectivity.OpenFormulaMarginValues
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.query
  OpenFormulaGateMetadata.atom OpenFormulaGateMetadata.kind

noncomputable def baseHomeomorph {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c) :
    PositiveReciprocalGraph.Base (PositiveMarginGraph.rootOn F c) ≃ₜ
      (Description.mk (ClosedFormulaGateMetadata.dimension c) p).realization := by
  let G:=TriangularContinuousGraph.homeomorph (F.dimension c) (PositiveMarginGraph.gate F c)
    (PositiveMarginGraph.gate_continuous F c) (F.count c)
  have HF (y : PositiveReciprocalGraph.Base (PositiveMarginGraph.rootOn F c)) :
      p.Holds (Formula.extend (G y.val)) := by
    apply (OpenFormulaMargin.positive_iff hp _).mp
    have H:=y.property
    rw [root_on_formula hp c hc hs] at H
    exact H
  have HI (x : (Description.mk (ClosedFormulaGateMetadata.dimension c) p).realization) :
      0<PositiveMarginGraph.rootOn F c (G.symm x.val) := by
    rw [root_on_formula hp c hc hs]
    have HE : TriangularContinuousGraph.projection (F.dimension c) (F.count c) (G.symm x.val).val=x.val := G.apply_symm_apply x.val
    rw [HE]
    exact (OpenFormulaMargin.positive_iff hp _).mpr x.property
  exact
    { toFun := fun y => ⟨G y.val,HF y⟩
      invFun := fun x => ⟨G.symm x.val,HI x⟩
      left_inv := fun y => Subtype.ext (G.symm_apply_apply y.val)
      right_inv := fun x => Subtype.ext (G.apply_symm_apply x.val)
      continuous_toFun := (G.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (G.symm.continuous.comp continuous_subtype_val).subtype_mk _ }

noncomputable def sourceHomeomorph {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c) :
    (PositiveMarginSource.description F c).realization ≃ₜ
      (Description.mk (ClosedFormulaGateMetadata.dimension c) p).realization :=
  (PositiveMarginGraph.reciprocalHomeomorph F c (source_scope c)).trans
    ((PositiveReciprocalGraph.homeomorph (PositiveMarginGraph.rootOn F c)
      (PositiveMarginValues.rootOn_continuous F c) (root_nonneg hp c hc hs)).trans (baseHomeomorph hp c hc hs))

theorem connected_iff {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c) :
    (PositiveMarginSource.description F c).Connected ↔ (Description.mk (ClosedFormulaGateMetadata.dimension c) p).Connected := by
  have HL:=PositiveMarginSource.description_wellFormed F c (source_scope c)
  have HO : (Description.mk (ClosedFormulaGateMetadata.dimension c) p).WellFormed := hs
  have HE:=(sourceHomeomorph hp c hc hs).isPreconnected_image (s := univ)
  rw [Set.image_univ_of_surjective (sourceHomeomorph hp c hc hs).surjective] at HE
  have HS {A : Type} [TopologicalSpace A] (T : Set A) : IsPreconnected T ↔ IsPreconnected (univ : Set T) :=
    isPreconnected_iff_preconnectedSpace.trans preconnectedSpace_iff_univ
  simp only [Description.Connected,HL,HO,true_and]
  exact (HS _).trans (HE.symm.trans (HS _).symm)

end LeanCanny.Connectivity.OpenFormulaMarginValues
