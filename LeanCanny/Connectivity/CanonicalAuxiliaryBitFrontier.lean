/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryCandidateValidity
public import LeanCanny.Connectivity.BitFrontierCover

/-! # Actual bounded Boolean frontier covers with native vertex validation

Every raw word denotes its decoded accessible piece or the empty piece.
Validity is native PSPACE. Edges below are the actual relative-frontier
relation; no native algorithm for those edges is asserted here.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalAuxiliaryBitFrontier
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR Set
open Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev width (d : Description) := CanonicalAuxiliaryCandidateCover.tagWidth (CanonicalSignRefinement.original d)
noncomputable def valid (original label : List Bool) : Bool :=
  decide (CanonicalAuxiliaryCandidateLabels.Valid (pair original label))

noncomputable def piece (d : Description) (i : Vertex (width d)) : Set d.realization :=
  if h : CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) i.val) then
    CanonicalAuxiliaryCandidateCover.piece d (CanonicalAuxiliaryCandidateLabels.decode d i.val h) else ∅

theorem decode_encode (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d)
    (h : CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) (CanonicalAuxiliaryCandidateCover.encode d i))) :
    CanonicalAuxiliaryCandidateLabels.decode d (CanonicalAuxiliaryCandidateCover.encode d i) h=i :=
  CanonicalAuxiliaryCandidateCover.encode_injective d (CanonicalAuxiliaryCandidateLabels.encode_decode d _ h)

theorem piece_encode (d : Description) (i : CanonicalAuxiliaryCandidateCover.Index d)
    (hi : (CanonicalAuxiliaryCandidateCover.piece d i).Nonempty) (hd : d.WellFormed) :
    piece d (CanonicalAuxiliaryCandidateCover.vertex d i)=CanonicalAuxiliaryCandidateCover.piece d i := by
  have HV:=(CanonicalAuxiliaryCandidateLabels.encoded_nonempty_iff d hd i).mp hi
  unfold piece CanonicalAuxiliaryCandidateCover.vertex
  rw [dite_eq_left HV,decode_encode]

theorem covers (d : Description) (hd : d.WellFormed) (x : d.realization) : ∃ i,x∈piece d i := by
  obtain ⟨i,hi⟩:=CanonicalAuxiliaryCandidateCover.covers d hd x
  refine ⟨CanonicalAuxiliaryCandidateCover.vertex d i,?_⟩
  rw [piece_encode d i ⟨x,hi⟩ hd]
  exact hi

theorem accessible (d : Description) (hd : d.WellFormed) (i : Vertex (width d)) : FrontierCover.Accessible (piece d i) := by
  unfold piece
  split_ifs
  · exact CanonicalAuxiliaryCandidateCover.accessible d hd _
  · intro x _ y hy
    exact False.elim (Set.not_nonempty_empty ⟨y,hy⟩)

theorem piece_nonempty_iff (d : Description) (hd : d.WellFormed) (i : Vertex (width d)) :
    (piece d i).Nonempty↔CanonicalAuxiliaryCandidateLabels.Valid (pair (CanonicalSignRefinement.original d) i.val) := by
  unfold piece
  split_ifs with hi
  · exact ⟨fun _=>hi,fun _=>CanonicalAuxiliaryCandidateLabels.decoded_nonempty d hd i.val hi⟩
  · exact iff_of_false Set.not_nonempty_empty hi

noncomputable def edge (d : Description) (a b : List Bool) : Bool :=
  if ha : a.length=width d then if hb : b.length=width d then
    decide (FrontierCover.Incident (piece d) ⟨a,ha⟩ ⟨b,hb⟩) else false else false

noncomputable def cover (d : Description) (hd : d.WellFormed) :
    BitFrontierCover d.realization (width d) (edge d) (valid (CanonicalSignRefinement.original d)) where
  piece := piece d
  cover := covers d hd
  accessible := accessible d hd
  valid_iff i := by rw [valid,decide_eq_true_eq]; exact (piece_nonempty_iff d hd i).symm
  edge_iff i j := by simp only [edge,dite_eq_left i.property,dite_eq_left j.property,decide_eq_true_eq]

theorem vertex_computable :
    ComputableTidilyInPolySpace (fun p : List Bool×List Bool=>valid p.1 p.2) (encPair encBits encBits) encBool := by
  have H:=CanonicalAuxiliaryCandidateLabels.decider.computable.comp (.of_polyTime (pair_computable
    (ComputableTidilyInPolyTime.fst encBits encBits) (ComputableTidilyInPolyTime.snd encBits encBits)))
  exact H.congr (fun _=>rfl)

theorem connected_language_iff (d : Description) (hd : d.WellFormed) :
    (Input.whole d).encode∈connectedLanguage ↔
      ImplicitGraph.Connected (edge d) (valid (CanonicalSignRefinement.original d)) (width d) := by
  rw [whole_encode_mem_iff]
  change (d.WellFormed ∧ IsPreconnected d.realization)↔_
  rw [isPreconnected_iff_preconnectedSpace,preconnectedSpace_iff_univ]
  exact ⟨fun h=>(cover d hd).isPreconnected_iff_connected.mp h.2,
    fun h=>⟨hd,(cover d hd).isPreconnected_iff_connected.mpr h⟩⟩

theorem point_language_iff (q : PointQuery) (hd : q.space.WellFormed) :
    (Input.point q).encode∈pointLanguage ↔
      ∃ x y : q.space.realization,
        Denotes q.space.dimension q.source x.val ∧ Denotes q.space.dimension q.target y.val ∧
        ∃ i j : Vertex (width q.space),x∈piece q.space i ∧ y∈piece q.space j ∧
          ImplicitGraph.Reachable (edge q.space) (valid (CanonicalSignRefinement.original q.space))
            (width q.space) i.val j.val := by
  rw [point_encode_mem_iff]
  constructor
  · rintro ⟨_,x,y,HX,HY,H⟩
    let a : q.space.realization:=⟨x,H.source_mem⟩
    let b : q.space.realization:=⟨y,H.target_mem⟩
    obtain ⟨i,HI⟩:=covers q.space hd a
    obtain ⟨j,HJ⟩:=covers q.space hd b
    refine ⟨a,b,HX,HY,i,j,HI,HJ,?_⟩
    apply ((cover q.space hd).joinedIn_iff_reachable i.property j.property HI HJ).mp
    exact joinedIn_univ.mpr ((joinedIn_iff_joined a.property b.property).mp H)
  · rintro ⟨x,y,HX,HY,i,j,HI,HJ,H⟩
    refine ⟨hd,x.val,y.val,HX,HY,?_⟩
    exact (joinedIn_iff_joined x.property y.property).mpr (joinedIn_univ.mp
      (((cover q.space hd).joinedIn_iff_reachable i.property j.property HI HJ).mpr H))
end LeanCanny.Connectivity.CanonicalAuxiliaryBitFrontier
