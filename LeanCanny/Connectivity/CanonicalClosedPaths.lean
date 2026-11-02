/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CompleteConnectedIsometricPath
public import LeanCanny.Connectivity.CanonicalClosedLocalTopology
/-! # Actual native closed-source components have constructed paths

The complete locally connected component embeds by its literal original
coordinate tuple into a finite real Banach space. Constructed ambient polyline
limits lift back to that SAME component. No path, recursive cover, compactness,
regularity or evaluator premise remains in this geometric cover construction.
Native bounded label and edge algorithms are separate obligations.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalClosedPaths
open Set LeanCanny.Geometry CanonicalClosedComponentCover
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotCircularBoundedCover.root

theorem paths (c : List Bool) : Paths c := by
  intro w x hx y hy
  let X := piece c w
  let : ConnectedSpace X := CanonicalClosedLocalTopology.piece_connected c w
  let : LocallyConnectedSpace X := CanonicalClosedLocalTopology.piece_locallyConnected c w
  let : CompleteSpace X := CanonicalClosedLocalTopology.piece_complete c w
  let e : X → (Fin (arity c) → ℝ) := fun z => z.val.val
  have HE : Isometry e := Isometry.of_dist_eq (fun _ _ => rfl)
  have H : Joined (⟨x,hx⟩ : X) ⟨y,hy⟩ := CompleteConnectedIsometricPath.joined e HE _ _
  exact (joinedIn_iff_joined hx hy).mpr H

noncomputable def closedCovers (d : Description) : CanonicalSignRefinement.ClosedCovers d :=
  CanonicalClosedComponentCover.closedCovers d (fun l => paths (CanonicalSignRefinement.source d l))
end LeanCanny.Connectivity.CanonicalClosedPaths
