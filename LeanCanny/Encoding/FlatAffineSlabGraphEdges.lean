/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSlabGraph

/-! # Encoded slab attachment edges are exactly the checked native queries -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSlabGraph
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
attribute [local irreducible] width descriptorWidth jointWidth branchNode markerNode

theorem branch_marker_iff (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c d w : List Bool)
    (hB : pair (pair (source c) (pair (sampleWord false c) (gapWord c))) d ∈ FlatAffineEndpointBranchLabels.language F cone height)
    (hM : pair (pair (source c) (endpointWord side c)) w ∈ FlatAffineEndpointMarkers.language F cone height) :
    pair c (pair (branchNode F cone height c d) (markerNode F cone height side c w)) ∈ edgeLanguage F cone height ↔
      FlatAffineEndpointIncidenceQuery.record (source c) (endpointWord side c) (sampleWord side c) (gapWord c) d w ∈
        FlatAffineEndpointIncidenceQuery.language F cone height (!side) := by
  have HD : d.length = descriptorWidth F cone height c := by
    simpa only [FlatAffineEndpointBranchLabels.descriptor, FlatAffineEndpointBranchLabels.source,
      pairFst_pair, pairSnd_pair, descriptorWidth, jointWidth] using FlatAffineEndpointBranchLabels.valid_length F cone height _ hB
  have HW : w.length = jointWidth F cone height c := by
    simpa only [FlatAffineEndpointMarkers.jointWord, FlatAffineEndpointMarkers.source,
      pairFst_pair, pairSnd_pair, jointWidth] using FlatAffineEndpointMarkers.valid_length F cone height _ hM
  have VB := (branchNode_valid F cone height c d hB).2
  have VM := (markerNode_valid F cone height side c w hM).2
  simp only [edgeLanguage, Set.mem_ofPred_eq, leftVertex, rightVertex, pairFst_pair, pairSnd_pair, VB, VM, true_and]
  cases side <;> simp [rawEdgeLanguage, guardLanguage, tagPair, branchNode_kind, markerNode_kind,
    attachmentQuery_nodes F cone height _ c d w HD HW]

theorem marker_branch_iff (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c d w : List Bool)
    (hB : pair (pair (source c) (pair (sampleWord false c) (gapWord c))) d ∈ FlatAffineEndpointBranchLabels.language F cone height)
    (hM : pair (pair (source c) (endpointWord side c)) w ∈ FlatAffineEndpointMarkers.language F cone height) :
    pair c (pair (markerNode F cone height side c w) (branchNode F cone height c d)) ∈ edgeLanguage F cone height ↔
      FlatAffineEndpointIncidenceQuery.record (source c) (endpointWord side c) (sampleWord side c) (gapWord c) d w ∈
        FlatAffineEndpointIncidenceQuery.language F cone height (!side) := by
  have HD : d.length = descriptorWidth F cone height c := by
    simpa only [FlatAffineEndpointBranchLabels.descriptor, FlatAffineEndpointBranchLabels.source,
      pairFst_pair, pairSnd_pair, descriptorWidth, jointWidth] using FlatAffineEndpointBranchLabels.valid_length F cone height _ hB
  have HW : w.length = jointWidth F cone height c := by
    simpa only [FlatAffineEndpointMarkers.jointWord, FlatAffineEndpointMarkers.source,
      pairFst_pair, pairSnd_pair, jointWidth] using FlatAffineEndpointMarkers.valid_length F cone height _ hM
  have VB := (branchNode_valid F cone height c d hB).2
  have VM := (markerNode_valid F cone height side c w hM).2
  simp only [edgeLanguage, Set.mem_ofPred_eq, leftVertex, rightVertex, pairFst_pair, pairSnd_pair, VB, VM, true_and]
  cases side <;> simp [rawEdgeLanguage, guardLanguage, tagPair, branchNode_kind, markerNode_kind,
    swap, attachmentQuery_nodes F cone height _ c d w HD HW]

end LeanCanny.Encoding.FlatAffineSlabGraph
