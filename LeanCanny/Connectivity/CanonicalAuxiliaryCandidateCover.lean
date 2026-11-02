/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.AuxiliaryCandidateComponentCover
public import LeanCanny.Connectivity.CanonicalSignGraph
public import LeanCanny.Encoding.CanonicalSignSources

/-! # Bounded auxiliary labels refine arbitrary Boolean realizations

Every accepted original sign word uses the literal native closed circular
source and its auxiliary candidate component cover. Proper projection and
radial access retain the original permitted boundaries. Relative-frontier
edge evaluation remains an explicit missing algorithm.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def dimension (c : List Bool) :=
  BoundedMonotoneGateSource.total ClosedFormulaGateTruth.F (FormulaSignSlotCircularBoundedCover.root c)
noncomputable def equation (c : List Bool) :=
  BoundedMonotoneGateSource.polynomial ClosedFormulaGateTruth.F (FormulaSignSlotCircularBoundedCover.root c)

theorem dimension_unary : UnaryFn dimension :=
  (BoundedMonotoneGateSource.total_unary _ ClosedFormulaGateMetadata.access).comp FormulaSignSlotCircularBoundedCover.root_FP

theorem equation_FP : (fun c=>(equation c).toData.toBits)∈FP :=
  mem_FP_comp FormulaSignSlotCircularBoundedCover.root_FP
    (BoundedMonotoneGateSource.polynomial_FP _ ClosedFormulaGateMetadata.access)

attribute [local irreducible] FormulaSignSlotCircularBoundedCover.root
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom
  ClosedFormulaGateMetadata.kind Input.field pair FormulaView.normalize

theorem equation_scope (c : List Bool) : (equation c).arity≤dimension c := by
  unfold equation dimension
  exact BoundedMonotoneGateSource.polynomial_arity ClosedFormulaGateTruth.F
    (FormulaSignSlotCircularBoundedCover.root c)
    (ClosedFormulaGateTruth.source_scope (FormulaSignSlotCircularBoundedCover.root c))

noncomputable def width : List Bool→ℕ :=
  IntegralMixedAuxiliaryCandidate.labelWidth dimension_unary equation_FP equation_scope

theorem width_unary : UnaryFn width :=
  IntegralMixedAuxiliaryCandidate.labelWidth_unary dimension_unary equation_FP equation_scope

noncomputable def sourceHomeomorph (c : List Bool) :
    FormulaSignSlotCircularBoundedCover.Source c ≃ₜ AuxiliaryCandidateComponentCover.Space dimension equation c := by
  change {x : Fin (dimension c)→ℝ | (equation c).eval (Formula.extend x)=0} ≃ₜ
    {x : Fin (dimension c)→ℝ | (AuxiliaryTiltedTerm.polynomial (dimension c) (equation c)).eval x=0}
  apply Homeomorph.setCongr
  ext x
  change (equation c).eval (Formula.extend x)=0 ↔ (AuxiliaryTiltedTerm.polynomial (dimension c) (equation c)).eval x=0
  rw [AuxiliaryCandidateComponentCover.evaluation]

noncomputable def closedCover (c : List Bool) :
    ClopenPathCover (FormulaSignSlotCircularBoundedCover.Source c) (Vertex (width c)) :=
  (AuxiliaryCandidateComponentCover.cover dimension_unary equation_FP equation_scope c).comap (sourceHomeomorph c)

theorem closed_accessible (c : List Bool) (i : Vertex (width c)) :
    FrontierCover.Accessible ((closedCover c).piece i) := by
  intro x hx y hy
  have HX : x∈(closedCover c).piece i := ((closedCover c).clopen i).isClosed.closure_eq ▸ hx
  exact ((closedCover c).paths i x HX y hy).mono (subset_insert x _)

noncomputable def data (d : Description) : CanonicalSignRefinement.ClosedCovers d where
  Index l := Vertex (width (CanonicalSignRefinement.source d l))
  finite _ := inferInstance
  closedPiece l := (closedCover (CanonicalSignRefinement.source d l)).piece
  closedCover l := (closedCover (CanonicalSignRefinement.source d l)).cover
  closedAccess l := closed_accessible (CanonicalSignRefinement.source d l)

noncomputable abbrev Index (d : Description) :=
  (l : CanonicalSignRefinement.Label d) × Vertex (width (CanonicalSignRefinement.source d l))
noncomputable def piece (d : Description) (i : Index d) : Set d.realization := (data d).piece i
noncomputable def edge (d : Description) := FrontierCover.Incident (piece d)
noncomputable def walk (d : Description) := Relation.ReflTransGen (edge d)

theorem covers (d : Description) (hd : d.WellFormed) : ∀ x,∃ i,x∈piece d i :=
  CanonicalSignRefinement.ClosedCovers.cover hd (data d)

theorem accessible (d : Description) (hd : d.WellFormed) (i : Index d) : FrontierCover.Accessible (piece d i) :=
  CanonicalSignRefinement.ClosedCovers.accessible hd (data d) i

theorem connected_language_iff (d : Description) (hd : d.WellFormed) :
    (Input.whole d).encode∈connectedLanguage ↔
      ∀ i j : Index d,(piece d i).Nonempty→(piece d j).Nonempty→walk d i j :=
  CanonicalSignGraph.connected_language_iff d hd (data d)

theorem point_language_iff (q : PointQuery) (hd : q.space.WellFormed) :
    (Input.point q).encode∈pointLanguage ↔
      ∃ x y : q.space.realization,
        Denotes q.space.dimension q.source x.val ∧ Denotes q.space.dimension q.target y.val ∧
        ∃ i j : Index q.space,x∈piece q.space i ∧ y∈piece q.space j ∧ walk q.space i j :=
  CanonicalSignGraph.point_language_iff q hd (data q.space)
end LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover
