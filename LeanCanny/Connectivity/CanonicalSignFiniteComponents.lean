/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CanonicalSignSources
public import LeanCanny.Geometry.TermFiniteComponents
/-! # Finitely many components of the ACTUAL native closed sign sources

These literal source zero sets may be singular and unbounded. Their connected
components are finite and clopen, without a component or compactness premise.
This establishes connected covers; their path/accessibility and native bounded
label realizations remain separate obligations.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalSignFiniteComponents
open Set LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotCircularBoundedCover.root

theorem components_finite (c : List Bool) :
    Finite (ConnectedComponents (FormulaSignSlotCircularBoundedCover.Source c)) :=
  TermFiniteComponents.components_finite
    (BoundedMonotoneGateSource.polynomial ClosedFormulaGateTruth.F (FormulaSignSlotCircularBoundedCover.root c))
    (BoundedMonotoneGateSource.total ClosedFormulaGateTruth.F (FormulaSignSlotCircularBoundedCover.root c))

theorem component_clopen (c : List Bool) (x : FormulaSignSlotCircularBoundedCover.Source c) :
    IsClopen (connectedComponent x) := by
  let : Finite (ConnectedComponents (FormulaSignSlotCircularBoundedCover.Source c)) := components_finite c
  exact FiniteComponentCover.isClopen_component x
end LeanCanny.Connectivity.CanonicalSignFiniteComponents
