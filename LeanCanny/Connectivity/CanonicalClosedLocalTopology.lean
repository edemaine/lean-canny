/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.TermLocallyConnected
public import LeanCanny.Connectivity.CanonicalClosedComponentCover
/-! # Complete locally connected topology of the actual native component pieces

All premises of the complete-metric path construction are discharged for the
literal closed-source components. This file does not assert the still separate
Mazurkiewicz–Moore–Menger path theorem or any effective/native bound.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalClosedLocalTopology
open Set LeanCanny.Geometry CanonicalClosedComponentCover
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotCircularBoundedCover.root

theorem locallyConnected (c : List Bool) : LocallyConnectedSpace (FormulaSignSlotCircularBoundedCover.Source c) :=
  TermLocallyConnected.locallyConnected (term c) (arity c)

theorem complete (c : List Bool) : CompleteSpace (FormulaSignSlotCircularBoundedCover.Source c) :=
  TermLocallyConnected.complete (term c) (arity c)

theorem piece_locallyConnected (c : List Bool) (w : Index c) : LocallyConnectedSpace (piece c w) := by
  let : LocallyConnectedSpace (FormulaSignSlotCircularBoundedCover.Source c) := locallyConnected c
  exact (piece_clopen c w).isOpen.locallyConnectedSpace

theorem piece_complete (c : List Bool) (w : Index c) : CompleteSpace (piece c w) := by
  let : CompleteSpace (FormulaSignSlotCircularBoundedCover.Source c) := complete c
  exact (piece_clopen c w).isClosed.isComplete.completeSpace_coe

theorem piece_connected (c : List Bool) (w : Index c) : ConnectedSpace (piece c w) :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent
end LeanCanny.Connectivity.CanonicalClosedLocalTopology
