/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.TermComponentSamples
public import LeanCanny.Connectivity.CanonicalSignFiniteComponents
public import LeanCanny.Connectivity.CanonicalSignRefinement
/-! # Actual finite sample labels cover the native closed-source components

The labels are zeros of the constructed coercive trailing grid that also
satisfy the literal native source equation. Pieces are their actual connected
components; finiteness, coverage and closedness are proved, even for singular
unbounded sources. To obtain the path covers needed by the connectivity graph,
ONLY within-component paths remain a geometric premise. Native label encodings
and component-membership algorithms are not asserted here.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalClosedComponentCover
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotCircularBoundedCover.root

noncomputable def term (c : List Bool) := BoundedMonotoneGateSource.polynomial ClosedFormulaGateTruth.F (FormulaSignSlotCircularBoundedCover.root c)
noncomputable def arity (c : List Bool) := BoundedMonotoneGateSource.total ClosedFormulaGateTruth.F (FormulaSignSlotCircularBoundedCover.root c)
noncomputable abbrev Index (c : List Bool) := TermComponentSamples.Sample (term c) (arity c)
instance (c : List Bool) : Finite (Index c) := TermComponentSamples.finite _ _
noncomputable def point (c : List Bool) (w : Index c) : FormulaSignSlotCircularBoundedCover.Source c :=
  TermComponentSamples.point (term c) (arity c) w
noncomputable def piece (c : List Bool) (w : Index c) : Set (FormulaSignSlotCircularBoundedCover.Source c) := connectedComponent (point c w)

theorem point_coordinate (c : List Bool) (w : Index c) (i : Fin (arity c)) : (point c w).val i=w.val.val i := rfl

theorem cover (c : List Bool) : ∀ x, ∃ w : Index c, x∈piece c w := TermComponentSamples.cover _ _

theorem piece_clopen (c : List Bool) (w : Index c) : IsClopen (piece c w) := CanonicalSignFiniteComponents.component_clopen c (point c w)

theorem piece_preconnected (c : List Bool) (w : Index c) : IsPreconnected (piece c w) := isPreconnected_connectedComponent

def Paths (c : List Bool) : Prop := ∀ w : Index c, ∀ x∈piece c w, ∀ y∈piece c w, JoinedIn (piece c w) x y

theorem accessible (c : List Bool) (h : Paths c) (w : Index c) : FrontierCover.Accessible (piece c w) := by
  intro x hx y hy
  have HX : x∈piece c w := (piece_clopen c w).isClosed.closure_eq ▸ hx
  exact (h w x HX y hy).mono (subset_insert x _)

noncomputable def closedCovers (d : Description)
    (h : ∀ l : CanonicalSignRefinement.Label d, Paths (CanonicalSignRefinement.source d l)) :
    CanonicalSignRefinement.ClosedCovers d where
  Index l := Index (CanonicalSignRefinement.source d l)
  finite _ := inferInstance
  closedPiece l := piece (CanonicalSignRefinement.source d l)
  closedCover l := cover (CanonicalSignRefinement.source d l)
  closedAccess l := accessible (CanonicalSignRefinement.source d l) (h l)
end LeanCanny.Connectivity.CanonicalClosedComponentCover
