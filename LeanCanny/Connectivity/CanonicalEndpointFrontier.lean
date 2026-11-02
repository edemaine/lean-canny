/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.CanonicalAuxiliaryBitFrontier
public import LeanCanny.Connectivity.EndpointSingletonPieces
public import LeanCanny.Connectivity.BitEndpointFrontierNative

/-! # Fixed endpoint words for the actual Boolean frontier cover

The endpoint formulas themselves define the two added singleton pieces.
Reachability therefore needs no search for a piece containing either point.
The edges remain the actual relative-frontier relation, without a native
space claim for that relation.
-/
@[expose] public section
namespace LeanCanny.Connectivity.CanonicalEndpointFrontier
open Set ETR Computation Turing.MultiTapeTM
open scoped Classical

noncomputable abbrev width (q : PointQuery) := CanonicalAuxiliaryBitFrontier.width q.space+2
noncomputable def sourcePiece (q : PointQuery) := EndpointSingletonPieces.piece q.space q.source
noncomputable def targetPiece (q : PointQuery) := EndpointSingletonPieces.piece q.space q.target
noncomputable def valid (q : PointQuery) :=
  BitEndpointFrontier.valid (CanonicalAuxiliaryBitFrontier.width q.space)
    (CanonicalAuxiliaryBitFrontier.valid (CanonicalSignRefinement.original q.space))
    (decide (sourcePiece q).Nonempty) (decide (targetPiece q).Nonempty)
noncomputable def edge (q : PointQuery) :=
  BitEndpointFrontier.edge (CanonicalAuxiliaryBitFrontier.piece q.space) (sourcePiece q) (targetPiece q)

noncomputable def cover (q : PointQuery) (hd : q.space.WellFormed) :
    BitFrontierCover q.space.realization (width q) (edge q) (valid q) :=
  BitEndpointFrontier.cover (CanonicalAuxiliaryBitFrontier.cover q.space hd) (sourcePiece q) (targetPiece q)
    (EndpointSingletonPieces.accessible q.space q.source) (EndpointSingletonPieces.accessible q.space q.target)

theorem point_language_iff (q : PointQuery) (hd : q.space.WellFormed) :
    (Input.point q).encode∈pointLanguage ↔
      ImplicitGraph.Reachable (edge q) (valid q) (width q)
        (BitEndpointFrontier.source (CanonicalAuxiliaryBitFrontier.width q.space))
        (BitEndpointFrontier.target (CanonicalAuxiliaryBitFrontier.width q.space)) := by
  rw [point_encode_mem_iff]
  constructor
  · rintro ⟨_,x,y,HX,HY,H⟩
    let a : q.space.realization:=⟨x,H.source_mem⟩
    let b : q.space.realization:=⟨y,H.target_mem⟩
    apply (BitEndpointFrontier.joinedIn_iff (CanonicalAuxiliaryBitFrontier.cover q.space hd)
      (sourcePiece q) (targetPiece q) (EndpointSingletonPieces.accessible q.space q.source)
      (EndpointSingletonPieces.accessible q.space q.target) (x:=a) (y:=b) HX HY).mp
    exact joinedIn_univ.mpr ((joinedIn_iff_joined a.property b.property).mp H)
  · intro h
    have HS : (sourcePiece q).Nonempty := by
      have HV:=((cover q hd).valid_iff
        ⟨BitEndpointFrontier.source (CanonicalAuxiliaryBitFrontier.width q.space),BitEndpointFrontier.source_length _⟩).mp h.1
      change (BitEndpointFrontier.rawPiece (CanonicalAuxiliaryBitFrontier.piece q.space)
        (sourcePiece q) (targetPiece q) (BitEndpointFrontier.source (CanonicalAuxiliaryBitFrontier.width q.space))).Nonempty at HV
      simpa only [BitEndpointFrontier.rawPiece_source] using HV
    have HT : (targetPiece q).Nonempty := by
      have HV:=((cover q hd).valid_iff
        ⟨BitEndpointFrontier.target (CanonicalAuxiliaryBitFrontier.width q.space),BitEndpointFrontier.target_length _⟩).mp h.2.1
      change (BitEndpointFrontier.rawPiece (CanonicalAuxiliaryBitFrontier.piece q.space)
        (sourcePiece q) (targetPiece q) (BitEndpointFrontier.target (CanonicalAuxiliaryBitFrontier.width q.space))).Nonempty at HV
      simpa only [BitEndpointFrontier.rawPiece_target] using HV
    obtain ⟨x,HX⟩:=HS
    obtain ⟨y,HY⟩:=HT
    refine ⟨hd,x.val,y.val,HX,HY,?_⟩
    apply (joinedIn_iff_joined x.property y.property).mpr
    apply joinedIn_univ.mp
    exact (BitEndpointFrontier.joinedIn_iff (CanonicalAuxiliaryBitFrontier.cover q.space hd)
      (sourcePiece q) (targetPiece q) (EndpointSingletonPieces.accessible q.space q.source)
      (EndpointSingletonPieces.accessible q.space q.target) HX HY).mpr h

end LeanCanny.Connectivity.CanonicalEndpointFrontier
