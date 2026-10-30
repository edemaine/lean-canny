/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabPrefixLabels
public import LeanCanny.Encoding.FlatAffineEndpointAncestorMatch

/-! # Actual branch endpoints retain the computed interior ancestor word -/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes (source endpointWord sampleWord)
open FlatAffineSlabGraphArcs (original Index)
open FlatAffineSlabGraphContext (endpointValue sampleValue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineJointCopyPrefixChoice.value FlatAffineJointPrefixChoice.value
  FlatAffineBranchPrefixChoice.value

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate F}
  {height : (u : List Bool) → Fin (count F u)} {c : List Bool}

noncomputable def Family.endpointPrefixWord (B : Family F cone height c) (side : Bool) (j : Index F cone height c) : List Bool :=
  FlatAffineJointCopyPrefixChoice.value F cone height 1 (pair (source c) (B.reference side j))

theorem Family.endpointPrefixWord_valid (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (hold : (height (original c)).val < FlatAffineFullSourceTower.count F (original c))
    (side : Bool) (j : Index F cone height c) :
    SquareSampleCompleteVertices.Valid (FlatAffineJointPrefixChoice.target F cone height) (source c) (B.endpointPrefixWord side j) :=
  FlatAffineJointCopyPrefixChoice.value_valid F cone height 1 (source c) (B.reference side j) hc.1 hold (B.valid side j)

theorem Family.endpointPrefixWord_point (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (hold : (height (original c)).val < FlatAffineFullSourceTower.count F (original c))
    (side : Bool) (j : Index F cone height c) :
    (SquareSampleCompleteVertices.candidate (FlatAffineJointPrefixChoice.target F cone height) (source c)
      (B.endpointPrefixWord side j) (B.endpointPrefixWord_valid hc hold side j)).val =
      B.curve j (endpointValue F cone height side c) ∘
        FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
          (FlatAffineShiftPrefixInput.depth_le F height) (original c) := by
  have HP := FlatAffineJointCopyPrefixChoice.value_point F cone height 1 (source c) (B.reference side j) hc.1 hold (B.valid side j)
  exact HP.trans (congrArg (fun f => f ∘ FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
    (FlatAffineShiftPrefixInput.depth_le F height) (original c)) (B.endpoint side j))

theorem Family.reference_marker_valid (B : Family F cone height c) (side : Bool) (j : Index F cone height c) :
    pair (pair (source c) (endpointWord side c)) (B.reference side j) ∈ FlatAffineEndpointMarkers.language F cone height := by
  have H := B.adjacent side j
  refine ⟨?_, ?_⟩
  · simpa only [FlatAffineEndpointMarkers.jointQuery, FlatAffineEndpointMarkers.source, FlatAffineEndpointMarkers.jointWord,
      pairFst_pair, pairSnd_pair] using H.1
  · simpa only [FlatAffineEndpointMarkers.identityQuery, FlatAffineEndpointMarkers.jointQuery, FlatAffineEndpointMarkers.source,
      FlatAffineEndpointMarkers.jointWord, FlatAffineEndpointMarkers.endpointWord, FlatAffineEndpointFiniteAdjacent.endpointQuery,
      pairFst_pair, pairSnd_pair] using H.2.1

section
variable [Fintype (Index F cone height c)] [LinearOrder (Index F cone height c)]

theorem Family.endpointPrefixWord_same (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (hold : (height (original c)).val < FlatAffineFullSourceTower.count F (original c))
    (side : Bool) (j : Index F cone height c) : B.endpointPrefixWord side j = B.prefixWord side j := by
  have HE := B.endpointPrefixWord_point hc hold side j
  have HP := B.prefixWord_point hc hold side j
  have HAB := (FlatAffineSlabGraphContext.endpoints_lt F cone height c hc).le
  have HS := Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between F cone height side c hc)
  have HT : endpointValue F cone height side c ∈ Icc (endpointValue F cone height false c) (endpointValue F cone height true c) := by
    cases side
    · exact ⟨le_rfl, HAB⟩
    · exact ⟨HAB, le_rfl⟩
  have HC := B.frozen_prefix hold j ⟨_, HT⟩ ⟨_, HS⟩
  exact SquareSampleCompleteVertices.candidate_injective _ _ _ _
    (B.endpointPrefixWord_valid hc hold side j) (B.prefixWord_valid hc hold side j)
    (Subtype.ext (HE.trans (HC.trans HP.symm)))

theorem Family.reference_endpoint_filter (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (hold : (height (original c)).val < FlatAffineFullSourceTower.count F (original c))
    (side : Bool) (j : Index F cone height c) :
    pair (pair (pair (source c) (endpointWord side c)) (B.reference side j)) (B.prefixWord side j) ∈
      FlatAffineEndpointAncestorMatch.language F cone height := by
  refine ⟨?_, ?_⟩
  · simpa only [pairFst_pair] using B.reference_marker_valid side j
  · simpa only [Family.endpointPrefixWord, FlatAffineEndpointAncestorMatch.value, Function.comp_apply, FlatAffineEndpointMarkers.jointQuery,
      FlatAffineEndpointMarkers.source, FlatAffineEndpointMarkers.jointWord, pairFst_pair, pairSnd_pair] using
      B.endpointPrefixWord_same hc hold side j

end
end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
