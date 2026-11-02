/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalClosedPaths
public import LeanCanny.Connectivity.CanonicalSignGraph
/-! # Actual finite frontier graphs for arbitrary canonical Boolean inputs

The finite refinement and all within-component paths are constructed here;
no recursive-cover hypothesis remains. Graph edges use relative frontiers in
the ORIGINAL permitted Boolean realization. Quantitative native word bounds,
label membership and edge-evaluation algorithms remain separate obligations;
these semantic equivalences do not assert a PSPACE theorem.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalConnectivityGraph
open ETR Set CanonicalSignRefinement CanonicalSignRefinement.ClosedCovers
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def data (d : Description) := CanonicalClosedPaths.closedCovers d
noncomputable abbrev Index (d : Description) := (data d).Tag
instance (d : Description) : Finite (Index d) := inferInstance
noncomputable def piece (d : Description) (i : Index d) : Set d.realization := (data d).piece i
noncomputable def edge (d : Description) := FrontierCover.Incident (piece d)
noncomputable def walk (d : Description) := Relation.ReflTransGen (edge d)

theorem cover (d : Description) (hd : d.WellFormed) : ∀ x, ∃ i, x∈piece d i := ClosedCovers.cover hd (data d)
theorem accessible (d : Description) (hd : d.WellFormed) (i : Index d) : FrontierCover.Accessible (piece d i) :=
  ClosedCovers.accessible hd (data d) i

theorem connected_language_iff (d : Description) (hd : d.WellFormed) :
    (Input.whole d).encode∈connectedLanguage ↔
      ∀ i j : Index d, (piece d i).Nonempty → (piece d j).Nonempty → walk d i j :=
  CanonicalSignGraph.connected_language_iff d hd (data d)

theorem point_language_iff (q : PointQuery) (hd : q.space.WellFormed) :
    (Input.point q).encode∈pointLanguage ↔
      ∃ x y : q.space.realization,
        Denotes q.space.dimension q.source x.val ∧ Denotes q.space.dimension q.target y.val ∧
        ∃ i j : Index q.space, x∈piece q.space i ∧ y∈piece q.space j ∧ walk q.space i j :=
  CanonicalSignGraph.point_language_iff q hd (data q.space)

theorem connected_iff_pathConnected (d : Description) : d.Connected ↔ d.PathConnected := by
  constructor
  · intro H
    let : PreconnectedSpace d.realization := isPreconnected_iff_preconnectedSpace.mp H.2
    refine ⟨H.1,?_⟩
    intro x hx y hy
    let a : d.realization := ⟨x,hx⟩
    let b : d.realization := ⟨y,hy⟩
    have HP : JoinedIn univ a b := FrontierCover.joinedIn_of_isPreconnected (piece d)
      (cover d H.1) (accessible d H.1) isPreconnected_univ (mem_univ a) (mem_univ b)
    exact (joinedIn_iff_joined hx hy).mpr (joinedIn_univ.mp HP)
  · exact Description.PathConnected.connected
end LeanCanny.Connectivity.CanonicalConnectivityGraph
