/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalSignRefinement
/-! # Exact canonical connectivity languages from the actual sign refinement

The graph is the relative-frontier graph inside the ORIGINAL Boolean
realization. Its edges attach only at permitted points. Recursive closed-source
covers remain explicit data; no graph-edge algorithm or polynomial-space
membership evaluator is assumed in these semantic equivalences.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalSignGraph
open ETR Set CanonicalSignRefinement CanonicalSignRefinement.ClosedCovers
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def edge {d : Description} (D : ClosedCovers d) := FrontierCover.Incident D.piece
noncomputable def walk {d : Description} (D : ClosedCovers d) := Relation.ReflTransGen (edge D)

theorem joined_iff {d : Description} (hd : d.WellFormed) (D : ClosedCovers d)
    {x y : d.realization} {i j : D.Tag} (hx : x∈D.piece i) (hy : y∈D.piece j) :
    JoinedIn univ x y ↔ walk D i j :=
  FrontierCover.joinedIn_iff_reachable D.piece (cover hd D) (accessible hd D) hx hy

theorem preconnected_iff {d : Description} (hd : d.WellFormed) (D : ClosedCovers d) :
    IsPreconnected d.realization ↔ ∀ i j, (D.piece i).Nonempty → (D.piece j).Nonempty → walk D i j := by
  rw [isPreconnected_iff_preconnectedSpace,preconnectedSpace_iff_univ]
  exact FrontierCover.isPreconnected_iff_reachable D.piece (cover hd D) (accessible hd D)

theorem connected_language_iff (d : Description) (hd : d.WellFormed) (D : ClosedCovers d) :
    (Input.whole d).encode∈connectedLanguage ↔
      ∀ i j, (D.piece i).Nonempty → (D.piece j).Nonempty → walk D i j := by
  rw [whole_encode_mem_iff]
  exact ⟨fun H => (preconnected_iff hd D).mp H.2,fun H => ⟨hd,(preconnected_iff hd D).mpr H⟩⟩

theorem point_language_iff (q : PointQuery) (hd : q.space.WellFormed) (D : ClosedCovers q.space) :
    (Input.point q).encode∈pointLanguage ↔
      ∃ x y : q.space.realization,
        Denotes q.space.dimension q.source x.val ∧ Denotes q.space.dimension q.target y.val ∧
        ∃ i j, x∈D.piece i ∧ y∈D.piece j ∧ walk D i j := by
  rw [point_encode_mem_iff]
  constructor
  · rintro ⟨_,x,y,HX,HY,H⟩
    let a : q.space.realization := ⟨x,H.source_mem⟩
    let b : q.space.realization := ⟨y,H.target_mem⟩
    obtain ⟨i,HI⟩ := cover hd D a
    obtain ⟨j,HJ⟩ := cover hd D b
    refine ⟨a,b,HX,HY,i,j,HI,HJ,(joined_iff hd D HI HJ).mp ?_⟩
    exact joinedIn_univ.mpr ((joinedIn_iff_joined a.property b.property).mp H)
  · rintro ⟨x,y,HX,HY,i,j,HI,HJ,H⟩
    refine ⟨hd,x.val,y.val,HX,HY,?_⟩
    exact (joinedIn_iff_joined x.property y.property).mpr (joinedIn_univ.mp ((joined_iff hd D HI HJ).mpr H))
end LeanCanny.Connectivity.CanonicalSignGraph
