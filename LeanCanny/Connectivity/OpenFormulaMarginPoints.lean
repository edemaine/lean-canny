/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.OpenFormulaMarginHomeomorph
public import LeanCanny.Connectivity.PositiveMarginCanonicalPoint
/-! # Exact original coordinates and singleton endpoints of the open margin graph -/
@[expose] public section
namespace LeanCanny.Connectivity.OpenFormulaMarginValues
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.query
  OpenFormulaGateMetadata.atom OpenFormulaGateMetadata.kind

theorem sourceHomeomorph_val {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (z : (PositiveMarginSource.description F c).realization) (i : Fin (ClosedFormulaGateMetadata.dimension c)) :
    (sourceHomeomorph hp c hc hs z).val i=z.val ⟨i.val,by
      have HI : i.val<F.dimension c := i.isLt
      change i.val<F.dimension c+F.count c+1
      omega⟩ := rfl

noncomputable def sourcePoint {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (x : (Description.mk (ClosedFormulaGateMetadata.dimension c) p).realization) : (PositiveMarginSource.description F c).realization := by
  refine ⟨PositiveMarginGraph.point F c x.val,?_⟩
  change (PositiveMarginSource.source F c).Holds (Formula.extend (PositiveMarginGraph.point F c x.val))
  unfold PositiveMarginGraph.point
  rw [PositiveMarginGraph.appendHomeomorph_apply,PositiveMarginGraph.source_append F c _ _ (source_scope c)]
  have HP : 0<(PositiveMarginSource.root F c).eval (Formula.extend (PositiveMarginValues.full F c x.val)) := by
    rw [root_formula hp c hc hs]
    exact (OpenFormulaMargin.positive_iff hp _).mpr x.property
  exact ⟨by rw [PositiveMarginGraph.reciprocalValue,ite_eq_right HP.ne',inv_mul_cancel₀ HP.ne'],
    TriangularContinuousGraph.equations _ _ x.val _⟩

theorem sourceHomeomorph_sourcePoint {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (x : (Description.mk (ClosedFormulaGateMetadata.dimension c) p).realization) :
    sourceHomeomorph hp c hc hs (sourcePoint hp c hc hs x)=x := by
  apply Subtype.ext
  funext i
  rw [sourceHomeomorph_val]
  exact PositiveMarginGraph.point_old F c x.val i

noncomputable def pointQuery (c : List Bool) (s d : Formula) : PointQuery :=
  ⟨PositiveMarginSource.description F c,PositiveMarginSource.endpoint F s c,PositiveMarginSource.endpoint F d c⟩

theorem sourcePoint_denotes {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (s : Formula) (x : (Description.mk (ClosedFormulaGateMetadata.dimension c) p).realization)
    (hS : Denotes (ClosedFormulaGateMetadata.dimension c) s x.val) :
    Denotes (PositiveMarginSource.total F c) (PositiveMarginSource.endpoint F s c) (sourcePoint hp c hc hs x).val :=
  PositiveMarginGraph.endpoint_denotes F c s (source_scope c) x.val hS

private theorem homeomorph_joined {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x y : X) : JoinedIn univ x y ↔ JoinedIn univ (e x) (e y) := by
  constructor
  · intro H
    exact (H.map e.continuous.continuousOn).mono (subset_univ _)
  · intro H
    simpa only [Homeomorph.symm_apply_apply] using (H.map e.symm.continuous.continuousOn).mono (subset_univ _)

theorem ambient_joined_iff {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (y z : (PositiveMarginSource.description F c).realization) :
    JoinedIn (PositiveMarginSource.description F c).realization y.val z.val ↔
      JoinedIn (Description.mk (ClosedFormulaGateMetadata.dimension c) p).realization
        (sourceHomeomorph hp c hc hs y).val (sourceHomeomorph hp c hc hs z).val := by
  rw [joinedIn_iff_joined y.property z.property,← joinedIn_univ,
    homeomorph_joined (sourceHomeomorph hp c hc hs),joinedIn_univ,
    ← joinedIn_iff_joined (sourceHomeomorph hp c hc hs y).property (sourceHomeomorph hp c hc hs z).property]

theorem reachable_iff {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (s d : Formula) (x y : (Description.mk (ClosedFormulaGateMetadata.dimension c) p).realization)
    (hS : Denotes (ClosedFormulaGateMetadata.dimension c) s x.val) (hD : Denotes (ClosedFormulaGateMetadata.dimension c) d y.val) :
    (pointQuery c s d).Reachable ↔ (PointQuery.mk (Description.mk (ClosedFormulaGateMetadata.dimension c) p) s d).Reachable := by
  unfold pointQuery
  rw [PointQuery.reachable_iff (sourcePoint_denotes hp c hc hs s x hS) (sourcePoint_denotes hp c hc hs d y hD),
    PointQuery.reachable_iff hS hD]
  have HL:=PositiveMarginSource.description_wellFormed F c (source_scope c)
  have HO : (Description.mk (ClosedFormulaGateMetadata.dimension c) p).WellFormed := hs
  simp only [HL,HO,true_and]
  have HJ:=ambient_joined_iff hp c hc hs (sourcePoint hp c hc hs x) (sourcePoint hp c hc hs y)
  have HX:=sourceHomeomorph_sourcePoint hp c hc hs x
  have HY:=sourceHomeomorph_sourcePoint hp c hc hs y
  rw [HX,HY] at HJ
  exact HJ

end LeanCanny.Connectivity.OpenFormulaMarginValues
