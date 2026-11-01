/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ClosedFormulaGateReduction
public import LeanCanny.Connectivity.MonotoneGatePointSource
/-! # The literal native endpoint lift preserves actual closed-formula point queries -/
@[expose] public section
namespace LeanCanny.Connectivity.ClosedFormulaGateTruth
open ETR Set LeanCanny.Encoding LeanCanny.Computation LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom
  ClosedFormulaGateMetadata.kind

noncomputable def liftedPoint {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c)
    (x : (Description.mk (F.dimension c) p).realization) : MonotoneGateGraph.ZeroSet F c :=
  MonotoneGateCanonicalPoint.sourcePoint F c (source_scope c) ClosedFormulaGateMetadata.kind_ne_three
    ((baseHomeomorph hp c hc hs).symm x)

theorem originalProjection_liftedPoint {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c)
    (x : (Description.mk (F.dimension c) p).realization) :
    originalProjection hp c hc hs (liftedPoint hp c hc hs x)=x := by
  unfold originalProjection liftedPoint
  rw [MonotoneGateCanonicalPoint.projection_sourcePoint]
  exact (baseHomeomorph hp c hc hs).apply_symm_apply x

noncomputable def pointQuery (c : List Bool) (s d : Formula) : PointQuery :=
  ⟨MonotoneGateGraph.description F c,MonotoneGateEndpoint.endpoint F s c,MonotoneGateEndpoint.endpoint F d c⟩

theorem liftedPoint_denotes {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c)
    (s : Formula) (x : (Description.mk (F.dimension c) p).realization) (hx : Denotes (F.dimension c) s x.val) :
    Denotes (MonotoneGateGraph.total F c) (MonotoneGateEndpoint.endpoint F s c) (liftedPoint hp c hc hs x).val :=
  MonotoneGateCanonicalPoint.endpoint_denotes F c s (source_scope c) x.val hx

theorem ambient_joined_iff {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c)
    (y z : MonotoneGateGraph.ZeroSet F c) :
    JoinedIn (MonotoneGateGraph.description F c).realization y.val z.val ↔
      JoinedIn (Description.mk (F.dimension c) p).realization
        (originalProjection hp c hc hs y).val (originalProjection hp c hc hs z).val := by
  change JoinedIn (MonotoneGateGraph.ZeroSet F c) y.val z.val ↔ _
  rw [joinedIn_iff_joined y.property z.property,← joinedIn_univ,
    original_joined_iff hp c hc hs,joinedIn_univ,
    ← joinedIn_iff_joined (originalProjection hp c hc hs y).property (originalProjection hp c hc hs z).property]
  rfl

theorem reachable_iff {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c)
    (s d : Formula) (x y : (Description.mk (F.dimension c) p).realization)
    (hx : Denotes (F.dimension c) s x.val) (hy : Denotes (F.dimension c) d y.val) :
    (pointQuery c s d).Reachable ↔ (PointQuery.mk (Description.mk (F.dimension c) p) s d).Reachable := by
  unfold pointQuery
  rw [PointQuery.reachable_iff (liftedPoint_denotes hp c hc hs s x hx) (liftedPoint_denotes hp c hc hs d y hy),
    PointQuery.reachable_iff hx hy]
  have HL := MonotoneGateGraph.description_wellFormed F c (source_scope c)
  have HO : (Description.mk (F.dimension c) p).WellFormed := hs
  simp only [HL,HO,true_and]
  simpa only [originalProjection_liftedPoint] using ambient_joined_iff hp c hc hs (liftedPoint hp c hc hs x) (liftedPoint hp c hc hs y)

theorem point_language_iff {p : Formula} (hp : ClosedFormulaWitness.Closed p)
    (c : List Bool) (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤F.dimension c)
    (s d : Formula) (x y : (Description.mk (F.dimension c) p).realization)
    (hx : Denotes (F.dimension c) s x.val) (hy : Denotes (F.dimension c) d y.val) :
    (Input.point (pointQuery c s d)).encode∈pointLanguage ↔
      (Input.point (PointQuery.mk (Description.mk (F.dimension c) p) s d)).encode∈pointLanguage := by
  simpa only [point_encode_mem_iff] using reachable_iff hp c hc hs s d x y hx hy

end LeanCanny.Connectivity.ClosedFormulaGateTruth
