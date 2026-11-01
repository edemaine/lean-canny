/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ClosedFormulaGatePoints
public import LeanCanny.Connectivity.EndpointValidation
/-! # Exact guarded point-language equivalence retains original singleton validation -/
@[expose] public section
namespace LeanCanny.Connectivity.ClosedFormulaGateTruth
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom
  ClosedFormulaGateMetadata.kind

theorem endpoint_projection_holds {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c)
    (s : Formula) (hS : s.arity≤F.dimension c) (z : MonotoneGateGraph.ZeroSet F c)
    (HZ : (MonotoneGateEndpoint.endpoint F s c).Holds (Formula.extend z.val)) :
    s.Holds (Formula.extend (originalProjection hp c hc hs z).val) := by
  have HOld : s.Holds (Formula.extend z.val) := HZ.1
  apply (s.holds_congr _ _ (fun i hi => ?_)).mp HOld
  have HI : i < F.dimension c := hi.trans_le hS
  have HT : i < MonotoneGateGraph.total F c := by
    dsimp [MonotoneGateGraph.total,MonotoneGateGraph.base]
    omega
  have HIM : i < ClosedFormulaGateMetadata.dimension c := HI
  simp only [Formula.extend,dite_eq_left HIM,dite_eq_left HT]
  exact (MonotoneGateCanonicalPoint.projection_val F c (source_scope c)
    ClosedFormulaGateMetadata.kind_ne_three z ⟨i,HI⟩).symm

theorem reachable_iff_of_denotes {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c)
    (s d : Formula) (a b : Fin (F.dimension c) → ℝ)
    (hS : Denotes (F.dimension c) s a) (hD : Denotes (F.dimension c) d b) :
    (pointQuery c s d).Reachable ↔ (PointQuery.mk (Description.mk (F.dimension c) p) s d).Reachable := by
  constructor
  · rintro ⟨_,y,z,HY,HZ,HJ⟩
    let Y : MonotoneGateGraph.ZeroSet F c := ⟨y,HJ.source_mem⟩
    let Z : MonotoneGateGraph.ZeroSet F c := ⟨z,HJ.target_mem⟩
    have HYa : (originalProjection hp c hc hs Y).val=a := (hS.2 _).mp
      (endpoint_projection_holds hp c hc hs s hS.1 Y ((HY.2 y).mpr rfl))
    have HZb : (originalProjection hp c hc hs Z).val=b := (hD.2 _).mp
      (endpoint_projection_holds hp c hc hs d hD.1 Z ((HZ.2 z).mpr rfl))
    apply (PointQuery.reachable_iff hS hD).mpr
    refine ⟨hs,?_⟩
    rw [← HYa,← HZb]
    exact (ambient_joined_iff hp c hc hs Y Z).mp HJ
  · rintro ⟨HW,x,y,HX,HY,HJ⟩
    let X : (Description.mk (F.dimension c) p).realization := ⟨x,HJ.source_mem⟩
    let Y : (Description.mk (F.dimension c) p).realization := ⟨y,HJ.target_mem⟩
    exact (reachable_iff hp c hc hs s d X Y HX HY).mpr ⟨HW,x,y,HX,HY,HJ⟩

theorem point_language_guarded_iff {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c)
    (s d : Formula) :
    (Input.point (PointQuery.mk (Description.mk (F.dimension c) p) s d)).encode∈pointLanguage ↔
      (Input.point (PointQuery.mk (Description.mk (F.dimension c) p) s d)).encode∈EndpointValidation.validEndpointLanguage ∧
      (Input.point (pointQuery c s d)).encode∈pointLanguage := by
  rw [point_encode_mem_iff,EndpointValidation.validEndpoint_encode,point_encode_mem_iff]
  constructor
  · rintro ⟨HW,a,b,HA,HB,HJ⟩
    exact ⟨⟨⟨a,HA⟩,⟨b,HB⟩⟩,(reachable_iff_of_denotes hp c hc hs s d a b HA HB).mpr ⟨HW,a,b,HA,HB,HJ⟩⟩
  · rintro ⟨⟨⟨a,HA⟩,⟨b,HB⟩⟩,H⟩
    exact (reachable_iff_of_denotes hp c hc hs s d a b HA HB).mp H

end LeanCanny.Connectivity.ClosedFormulaGateTruth
