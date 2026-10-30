/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabGraphVertices

/-! # Every native slab edge agrees with the actual geometric piece graph -/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes
open FlatAffineSlabGraphArcs (equation)
open FlatAffineSlabGraphContext (endpointValue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local irreducible] branchPayload markerPayload FlatAffineEndpointMarkers.language
  FlatAffineEndpointIncidenceQuery.language FlatAffineEndpointMarkerEquality.language

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate F}
  {height : (u : List Bool) → Fin (count F u)} {c : List Bool}

theorem markerEquality_iff (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (side : Bool) (w v : List Bool)
    (hw : pair (pair (source c) (endpointWord side c)) w ∈ FlatAffineEndpointMarkers.language F cone height)
    (hv : pair (pair (source c) (endpointWord side c)) v ∈ FlatAffineEndpointMarkers.language F cone height) :
    pair (pair (source c) (endpointWord side c)) (pair w v) ∈ FlatAffineEndpointMarkerEquality.language F cone height ↔
      markerPoint F cone height c w = markerPoint F cone height c v := by
  have W : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (source c) w := by
    simpa only [FlatAffineEndpointMarkers.source, FlatAffineEndpointMarkers.jointWord, pairFst_pair, pairSnd_pair] using
      FlatAffineEndpointMarkers.joint_valid F cone height _ hw
  have V : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (source c) v := by
    simpa only [FlatAffineEndpointMarkers.source, FlatAffineEndpointMarkers.jointWord, pairFst_pair, pairSnd_pair] using
      FlatAffineEndpointMarkers.joint_valid F cone height _ hv
  rw [markerPoint_packet F cone height c w W, markerPoint_packet F cone height c v V]
  exact FlatAffineEndpointMarkerEquality.packet F cone height (source c) (endpointWord side c) w v hc.1 W V
    (FlatAffineSlabGraphContext.endpoint_label_valid F cone height side c hc) hw hv

variable [Fintype (FlatAffineSlabGraphArcs.Index F cone height c)] [LinearOrder (FlatAffineSlabGraphArcs.Index F cone height c)]

theorem Family.edge_iff (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (w v : List Bool)
    (i j : PieceIndex F cone height c) (hi : B.Denotes w i) (hj : B.Denotes v j) :
    pair c (pair w v) ∈ FlatAffineSlabGraph.edgeLanguage F cone height ↔
      FiniteFiberSlab.Edge (equation F height c) B.curve (endpointValue F cone height false c) (endpointValue F cone height true c) i j := by
  have VI := (B.valid_iff_denotes hc w).mpr ⟨i, hi⟩
  have VJ := (B.valid_iff_denotes hc v).mpr ⟨j, hj⟩
  simp only [FlatAffineSlabGraph.edgeLanguage, Set.mem_ofPred_eq, leftVertex, rightVertex,
    pairFst_pair, pairSnd_pair, VI, VJ, true_and]
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  · have H : B.descriptor false i = B.descriptor false j ↔ i = j :=
      (B.descriptors_injective hc false).eq_iff
    simpa [FlatAffineSlabGraph.rawEdgeLanguage, FlatAffineSlabGraph.guardLanguage, FlatAffineSlabGraph.tagPair,
      FlatAffineSlabGraph.branchEquality, leftVertex, rightVertex, hi.1, hj.1, hi.2, hj.2, FiniteFiberSlab.Edge] using H
  · have H := B.attachment_iff hc false i (markerPayload F cone height (pair c v)) hj.2.1
    simpa [FlatAffineSlabGraph.rawEdgeLanguage, FlatAffineSlabGraph.guardLanguage, FlatAffineSlabGraph.tagPair,
      attachmentQuery, leftVertex, rightVertex, hi.1, hj.1, hi.2, hj.2.2, FiniteFiberSlab.Edge] using H
  · have H := B.attachment_iff hc true i (markerPayload F cone height (pair c v)) hj.2.1
    simpa [FlatAffineSlabGraph.rawEdgeLanguage, FlatAffineSlabGraph.guardLanguage, FlatAffineSlabGraph.tagPair,
      attachmentQuery, leftVertex, rightVertex, hi.1, hj.1, hi.2, hj.2.2, FiniteFiberSlab.Edge] using H
  · have H := B.attachment_iff hc false j (markerPayload F cone height (pair c w)) hi.2.1
    simpa [FlatAffineSlabGraph.rawEdgeLanguage, FlatAffineSlabGraph.guardLanguage, FlatAffineSlabGraph.tagPair,
      attachmentQuery, swap, leftVertex, rightVertex, hi.1, hj.1, hj.2, hi.2.2, FiniteFiberSlab.Edge] using H
  · have H := markerEquality_iff hc false (markerPayload F cone height (pair c w)) (markerPayload F cone height (pair c v)) hi.2.1 hj.2.1
    rw [hi.2.2, hj.2.2] at H
    simpa [FlatAffineSlabGraph.rawEdgeLanguage, FlatAffineSlabGraph.guardLanguage, FlatAffineSlabGraph.tagPair,
      markerEqualityQuery, leftVertex, rightVertex, hi.1, hj.1, FiniteFiberSlab.Edge, Subtype.ext_iff] using H
  · simp [FlatAffineSlabGraph.rawEdgeLanguage, FlatAffineSlabGraph.guardLanguage, FlatAffineSlabGraph.tagPair,
      hi.1, hj.1, FiniteFiberSlab.Edge]
  · have H := B.attachment_iff hc true j (markerPayload F cone height (pair c w)) hi.2.1
    simpa [FlatAffineSlabGraph.rawEdgeLanguage, FlatAffineSlabGraph.guardLanguage, FlatAffineSlabGraph.tagPair,
      attachmentQuery, swap, leftVertex, rightVertex, hi.1, hj.1, hj.2, hi.2.2, FiniteFiberSlab.Edge] using H
  · simp [FlatAffineSlabGraph.rawEdgeLanguage, FlatAffineSlabGraph.guardLanguage, FlatAffineSlabGraph.tagPair,
      hi.1, hj.1, FiniteFiberSlab.Edge]
  · have H := markerEquality_iff hc true (markerPayload F cone height (pair c w)) (markerPayload F cone height (pair c v)) hi.2.1 hj.2.1
    rw [hi.2.2, hj.2.2] at H
    simpa [FlatAffineSlabGraph.rawEdgeLanguage, FlatAffineSlabGraph.guardLanguage, FlatAffineSlabGraph.tagPair,
      markerEqualityQuery, leftVertex, rightVertex, hi.1, hj.1, FiniteFiberSlab.Edge, Subtype.ext_iff] using H

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
