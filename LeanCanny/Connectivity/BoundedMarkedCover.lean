/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.BitMarkedCover
public import LeanCanny.Geometry.BoundedMarkedComponents

/-! # Bounded original connectedness from the marked source graph

The regular source may have additional components. A cover piece is marked
when it intersects the old sphere zero set, described by the single actual
mark polynomial. Original connectedness is exactly reachability between
these marked pieces through the full valid cover graph.
-/

@[expose] public section
namespace LeanCanny.Connectivity
open Set Geometry Geometry.BoundedRegularSource Geometry.BoundedZeroSource LeanCanny.Algebra MvPolynomial Computation

theorem bounded_preconnected_iff_marked_graph {n w : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b)
    {edge : List Bool → List Bool → Bool} {valid marked : List Bool → Bool}
    (C : BitFrontierCover (BoundedRegularSource.Zeros q D b R) w edge valid)
    (hm : ∀ i : Vertex w, marked i.val = true ↔ (C.piece i ∩ Marked q D b R).Nonempty) :
    IsPreconnected (Bounded q R) ↔ ImplicitGraph.MarkedConnected edge valid marked w := by
  apply (preconnected_iff_marked q D b R hD hb).trans
  simpa only [Subtype.forall] using C.marked_components_iff_connected (Marked q D b R) marked hm

end LeanCanny.Connectivity
