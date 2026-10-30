/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabPrefixLabels
public import LeanCanny.Encoding.FlatAffineBranchAncestorMatch

/-! # Native ancestor filtering agrees with actual slab branches

The filter tests the exact frozen blocks of the geometric branch. Its answer
is identical at both retained descriptors, so auxiliary joint-witness choices
cannot change which parent-specific branch family is selected.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes (source)
open FlatAffineSlabGraphArcs (original Index)
open FlatAffineSlabGraphContext (sampleValue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineBranchPrefixChoice.value FlatAffineJointPrefixChoice.value
  FlatAffineEndpointBranchLabels.language

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate F}
  {height : (u : List Bool) → Fin (count F u)} {c : List Bool}
  [Fintype (Index F cone height c)] [LinearOrder (Index F cone height c)]

theorem Family.ancestor_filter_constant (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (hold : (height (original c)).val < FlatAffineFullSourceTower.count F (original c))
    (j : Index F cone height c) (v : List Bool) :
    pair (B.sampleQuery false j) v ∈ FlatAffineBranchAncestorMatch.language F cone height ↔
      pair (B.sampleQuery true j) v ∈ FlatAffineBranchAncestorMatch.language F cone height := by
  have HL (side : Bool) : B.sampleQuery side j ∈ FlatAffineEndpointBranchLabels.language F cone height :=
    (B.labels_iff hc side _).mpr ⟨j, rfl⟩
  simp only [FlatAffineBranchAncestorMatch.language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair,
    HL false, HL true, true_and, B.native_prefix_same hc hold j]

theorem Family.ancestor_filter_packet (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (hold : (height (original c)).val < FlatAffineFullSourceTower.count F (original c))
    (side : Bool) (j : Index F cone height c) (v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineJointPrefixChoice.target F cone height) (source c) v) :
    pair (B.sampleQuery side j) v ∈ FlatAffineBranchAncestorMatch.language F cone height ↔
      (SquareSampleCompleteVertices.candidate (FlatAffineJointPrefixChoice.target F cone height) (source c) v hv).val =
        B.curve j (sampleValue F cone height side c) ∘
          FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
            (FlatAffineShiftPrefixInput.depth_le F height) (original c) := by
  have HL : B.sampleQuery side j ∈ FlatAffineEndpointBranchLabels.language F cone height :=
    (B.labels_iff hc side _).mpr ⟨j, rfl⟩
  have HW := B.prefixWord_valid hc hold side j
  have HP := B.prefixWord_point hc hold side j
  simp only [FlatAffineBranchAncestorMatch.language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, HL, true_and]
  rw [← B.prefixWord_program side j]
  constructor
  · intro he
    subst v
    exact HP
  · intro he
    exact SquareSampleCompleteVertices.candidate_injective _ _ _ _ HW hv (Subtype.ext (HP.trans he.symm))

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
