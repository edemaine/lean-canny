/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.OpenFormulaMarginPoints
public import LeanCanny.Connectivity.EndpointValidation
/-! # Exact guarded point-language preservation for actual open margin sources -/
@[expose] public section
namespace LeanCanny.Connectivity.OpenFormulaMarginValues
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.query
  OpenFormulaGateMetadata.atom OpenFormulaGateMetadata.kind

theorem endpoint_projection_holds {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (s : Formula) (hS : s.arity≤ClosedFormulaGateMetadata.dimension c)
    (z : (PositiveMarginSource.description F c).realization)
    (HZ : (PositiveMarginSource.endpoint F s c).Holds (Formula.extend z.val)) :
    s.Holds (Formula.extend (sourceHomeomorph hp c hc hs z).val) := by
  have HOld : s.Holds (Formula.extend z.val) := HZ.1
  apply (s.holds_congr _ _ (fun i hi => ?_)).mp HOld
  have HI : i < ClosedFormulaGateMetadata.dimension c := hi.trans_le hS
  have HT : i < (PositiveMarginSource.description F c).dimension := by
    change i<F.dimension c+F.count c+1
    have HF : i<F.dimension c := HI
    omega
  simp only [Formula.extend,dite_eq_left HI,dite_eq_left HT]
  exact (sourceHomeomorph_val hp c hc hs z ⟨i,HI⟩).symm

theorem reachable_iff_of_denotes {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (s d : Formula) (a b : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ)
    (hS : Denotes (ClosedFormulaGateMetadata.dimension c) s a) (hD : Denotes (ClosedFormulaGateMetadata.dimension c) d b) :
    (pointQuery c s d).Reachable ↔ (PointQuery.mk (Description.mk (ClosedFormulaGateMetadata.dimension c) p) s d).Reachable := by
  constructor
  · rintro ⟨_,y,z,HY,HZ,HJ⟩
    let Y : (PositiveMarginSource.description F c).realization := ⟨y,HJ.source_mem⟩
    let Z : (PositiveMarginSource.description F c).realization := ⟨z,HJ.target_mem⟩
    have HYa : (sourceHomeomorph hp c hc hs Y).val=a := (hS.2 _).mp
      (endpoint_projection_holds hp c hc hs s hS.1 Y ((HY.2 y).mpr rfl))
    have HZb : (sourceHomeomorph hp c hc hs Z).val=b := (hD.2 _).mp
      (endpoint_projection_holds hp c hc hs d hD.1 Z ((HZ.2 z).mpr rfl))
    apply (PointQuery.reachable_iff hS hD).mpr
    refine ⟨hs,?_⟩
    rw [← HYa,← HZb]
    exact (ambient_joined_iff hp c hc hs Y Z).mp HJ
  · rintro ⟨HW,x,y,HX,HY,HJ⟩
    let X : (Description.mk (ClosedFormulaGateMetadata.dimension c) p).realization := ⟨x,HJ.source_mem⟩
    let Y : (Description.mk (ClosedFormulaGateMetadata.dimension c) p).realization := ⟨y,HJ.target_mem⟩
    exact (reachable_iff hp c hc hs s d X Y HX HY).mpr ⟨HW,x,y,HX,HY,HJ⟩

theorem point_language_guarded_iff {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (s d : Formula) :
    (Input.point (PointQuery.mk (Description.mk (ClosedFormulaGateMetadata.dimension c) p) s d)).encode∈pointLanguage ↔
      (Input.point (PointQuery.mk (Description.mk (ClosedFormulaGateMetadata.dimension c) p) s d)).encode∈EndpointValidation.validEndpointLanguage ∧
      (Input.point (pointQuery c s d)).encode∈pointLanguage := by
  rw [point_encode_mem_iff,EndpointValidation.validEndpoint_encode,point_encode_mem_iff]
  constructor
  · rintro ⟨HW,a,b,HA,HB,HJ⟩
    exact ⟨⟨⟨a,HA⟩,⟨b,HB⟩⟩,(reachable_iff_of_denotes hp c hc hs s d a b HA HB).mpr ⟨HW,a,b,HA,HB,HJ⟩⟩
  · rintro ⟨⟨⟨a,HA⟩,⟨b,HB⟩⟩,H⟩
    exact (reachable_iff_of_denotes hp c hc hs s d a b HA HB).mp H

theorem prepared_valid_of_valid (c : List Bool) (p s d : Formula)
    (H : (Input.point (PointQuery.mk (Description.mk (ClosedFormulaGateMetadata.dimension c) p) s d)).encode∈EndpointValidation.validEndpointLanguage) :
    (Input.point (pointQuery c s d)).encode∈EndpointValidation.validEndpointLanguage := by
  rw [EndpointValidation.validEndpoint_encode] at H ⊢
  obtain ⟨⟨a,HA⟩,⟨b,HB⟩⟩ := H
  exact ⟨⟨PositiveMarginGraph.point F c a,PositiveMarginGraph.endpoint_denotes F c s (source_scope c) a HA⟩,
    ⟨PositiveMarginGraph.point F c b,PositiveMarginGraph.endpoint_denotes F c d (source_scope c) b HB⟩⟩

end LeanCanny.Connectivity.OpenFormulaMarginValues
