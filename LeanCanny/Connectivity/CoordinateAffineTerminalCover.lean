/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.CoordinateAffineComponentCover
public import LeanCanny.Encoding.CoordinateAffineTerminalGraph
public import LeanCanny.Connectivity.BitClosedFrontierCover

/-! # Constructed native covers at the terminal coordinate stage

Complete critical labels cover every point of the finite terminal slice.
Their component pieces are clopen and path connected. The original native
terminal graph computes their exact overlaps, giving the accessible endpoint
cover needed by recursion, without a supplied geometric cover.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CoordinateAffineTerminalCover
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open CoordinateAffinePrefix (inputs)
open FlatAffineCompleteRootStages (next)
open FlatAffineCompleteChildLabels (parentCone)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] FlatAffineCompactComponentCover.piece FlatAffineCompactComponentCover.point FlatAffineCompactComponentCover.root

section
variable (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ) (level : List Bool → List Bool)
  (u v : List Bool)
variable (hv : FlatAffineCompleteVertices.Valid (inputs P depth objective level) (parentCone (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level)) u v)
  (hmax : P.dim u + 3 ≤ objective (FlatAffineFullSourceTower.stage u (depth u)))
include hv hmax

include hmax in
theorem edge_overlap (w z : List Bool) :
    CoordinateAffineTerminalGraph.edge P depth objective level (pair u v) w z = true ↔
      (FlatAffineCompactComponentCover.piece (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv w ∩ FlatAffineCompactComponentCover.piece (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv z).Nonempty := by
  by_cases HB : FlatAffineCompactComponentCover.Valid (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v w ∧ FlatAffineCompactComponentCover.Valid (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v z
  · obtain ⟨hw, hz⟩ := HB
    have HW := (FlatAffineCompleteChildLabels.valid (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u w v hw).1
    have HZ := (FlatAffineCompleteChildLabels.valid (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u z v hz).1
    rw [CoordinateAffineTerminalGraph.edge, decide_eq_true_eq]
    rw [CoordinateAffineTerminalReachability.packet P depth objective level u v w z hmax hv HW HZ]
    have HAw : pair u (pair w v) ∈ FlatAffineCompleteChildLabels.language (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) := hw
    have HAz : pair u (pair z v) ∈ FlatAffineCompleteChildLabels.language (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) := hz
    rw [and_iff_right HAw, and_iff_right HAz, FlatAffineCompactComponentCover.overlap_iff (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv w z hw hz]
    have EPw : (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv w hw).val =
        FlatAffineCompleteRootStages.newest (inputs P depth objective level) u (FlatAffineCompleteVertices.vertexEquiv (next (inputs P depth objective level)) (CoordinateAffineSliceRegularity.cone P depth objective level) u ⟨w, HW⟩).val ∘ Sum.inl := by
      unfold FlatAffineCompactComponentCover.point FlatAffineCompactComponentCover.root
      rfl
    have EPz : (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv z hz).val =
        FlatAffineCompleteRootStages.newest (inputs P depth objective level) u (FlatAffineCompleteVertices.vertexEquiv (next (inputs P depth objective level)) (CoordinateAffineSliceRegularity.cone P depth objective level) u ⟨z, HZ⟩).val ∘ Sum.inl := by
      unfold FlatAffineCompactComponentCover.point FlatAffineCompactComponentCover.root
      rfl
    rw [← EPw, ← EPz]
    change JoinedIn (FlatAffineCompactComponentCover.Slice (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv)
      (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv w hw).val
      (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv z hz).val ↔ _
    have HJ : JoinedIn (FlatAffineCompactComponentCover.Slice (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv) (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv w hw).val (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv z hz).val ↔ (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv z hz).val = (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv w hw).val :=
      CoordinateAffineTerminalSamples.joined_iff_eq P depth objective level u (FlatAffineCompleteVertices.vertexEquiv (inputs P depth objective level) (parentCone (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level)) u ⟨v, hv⟩) hmax (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv w hw).val (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv z hz).val (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv w hw).property
    have HC : (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv z hz).val ∈ connectedComponentIn (FlatAffineCompactComponentCover.Slice (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv) (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv w hw).val ↔ (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv z hz).val = (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv w hw).val :=
      CoordinateAffineTerminalSamples.component_iff_eq P depth objective level u (FlatAffineCompleteVertices.vertexEquiv (inputs P depth objective level) (parentCone (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level)) u ⟨v, hv⟩) hmax (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv w hw).val (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv z hz).val (FlatAffineCompactComponentCover.point (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv w hw).property
    exact HJ.trans HC.symm
  · constructor
    · intro HE
      have HH := CoordinateAffineTerminalGraph.edge_valid P depth objective level (pair u v) w z HE
      exact False.elim (HB ⟨(CoordinateAffineTerminalGraph.valid_packet P depth objective level u v w).mp HH.1,
        (CoordinateAffineTerminalGraph.valid_packet P depth objective level u v z).mp HH.2⟩)
    · rintro ⟨x, hx, hy⟩
      exact False.elim (HB ⟨(FlatAffineCompactComponentCover.piece_nonempty_iff (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv w).mp ⟨x, hx⟩,
        (FlatAffineCompactComponentCover.piece_nonempty_iff (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv z).mp ⟨x, hy⟩⟩)

noncomputable def pathCover : BitPathCover (FlatAffineCompactComponentCover.Slice (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv)
    (CoordinateAffineTerminalGraph.width P depth objective level (pair u v))
    (CoordinateAffineTerminalGraph.edge P depth objective level (pair u v))
    (CoordinateAffineTerminalGraph.valid P depth objective level (pair u v)) where
  piece i := FlatAffineCompactComponentCover.piece (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv i.val
  closed i := (CoordinateAffineComponentCover.piece_isClopen P depth objective level u v hv i.val).isClosed
  cover z := by
    obtain ⟨w, hw, hz⟩ := CoordinateAffineComponentCover.cover P depth objective level u v hv z
    have HL := FlatAffineCompactComponentCover.valid_width (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v w hw
    have HW : w.length = CoordinateAffineTerminalGraph.width P depth objective level (pair u v) := by
      simpa only [CoordinateAffineTerminalGraph.width, FlatAffineSliceRegularity.width, pairFst_pair] using HL
    exact ⟨⟨w, HW⟩, hz⟩
  paths i x hx y hy := by
    let : Finite (FlatAffineCompactComponentCover.Slice (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv) :=
      (CoordinateAffineTerminalSamples.finite_card_le P depth objective level u _ hmax).1
    let : TotallyDisconnectedSpace (FlatAffineCompactComponentCover.Slice (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv) := inferInstance
    have HS := (FlatAffineCompactComponentCover.piece_preconnected (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv i.val).subsingleton
    have HE : x = y := HS hx hy
    subst y
    exact JoinedIn.refl hx
  valid_iff i := by
    have HA : CoordinateAffineTerminalGraph.valid P depth objective level (pair u v) i.val = true ↔
        FlatAffineCompactComponentCover.Valid (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v i.val :=
      CoordinateAffineTerminalGraph.valid_packet P depth objective level u v i.val
    have HB : (FlatAffineCompactComponentCover.piece (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv i.val).Nonempty ↔
        FlatAffineCompactComponentCover.Valid (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v i.val :=
      FlatAffineCompactComponentCover.piece_nonempty_iff (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv i.val
    exact HA.trans HB.symm
  edge_iff i j := edge_overlap P depth objective level u v hv hmax i.val j.val

noncomputable def frontierCover : BitFrontierCover (FlatAffineCompactComponentCover.Slice (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv)
    (CoordinateAffineTerminalGraph.width P depth objective level (pair u v))
    (CoordinateAffineTerminalGraph.edge P depth objective level (pair u v))
    (CoordinateAffineTerminalGraph.valid P depth objective level (pair u v)) :=
  (pathCover P depth objective level u v hv hmax).toFrontier

include hmax in
theorem connected_iff : IsPreconnected (FlatAffineCompactComponentCover.Slice (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv) ↔
    pair u v ∈ CoordinateAffineTerminalGraph.connectedLanguage P depth objective level := by
  have H : IsPreconnected (FlatAffineCompactComponentCover.Slice (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv) ↔
      IsPreconnected (univ : Set (FlatAffineCompactComponentCover.Slice (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv)) :=
    isPreconnected_iff_preconnectedSpace.trans preconnectedSpace_iff_univ
  exact H.trans (frontierCover P depth objective level u v hv hmax).isPreconnected_iff_connected

noncomputable def componentCover : ClopenPathCover (FlatAffineCompactComponentCover.Slice (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level) u v hv)
    (Vertex (CoordinateAffineTerminalGraph.width P depth objective level (pair u v))) :=
  (frontierCover P depth objective level u v hv hmax).componentCover

end
end LeanCanny.Connectivity.CoordinateAffineTerminalCover
