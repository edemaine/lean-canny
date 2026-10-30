/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabFrozenPrefixes
public import LeanCanny.Connectivity.FlatAffineSlabBranchParents
public import LeanCanny.Encoding.FlatAffineBranchPrefixChoice

/-! # Computed branch ancestor labels agree at both retained samples

The native descriptor program computes a complete frozen ancestor word.
Its decoded point is precisely the earlier blocks of the actual branch.
Frozen-prefix constancy and uniqueness of complete labels make the two
sample words identical, independently of the chosen auxiliary joint tuples.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes (source)
open FlatAffineSlabGraphArcs (original Index)
open FlatAffineSlabGraphContext (sampleValue endpointValue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineBranchChoice.value FlatAffineJointPrefixChoice.value

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate F}
  {height : (u : List Bool) → Fin (count F u)} {c : List Bool}
  [Fintype (Index F cone height c)] [LinearOrder (Index F cone height c)]

noncomputable def Family.prefixWord (B : Family F cone height c) (side : Bool) (j : Index F cone height c) : List Bool :=
  FlatAffineJointPrefixChoice.value F cone height (pair (source c) (B.selectedWord side j))

omit [Fintype (Index F cone height c)] [LinearOrder (Index F cone height c)] in
theorem Family.prefixWord_program (B : Family F cone height c) (side : Bool) (j : Index F cone height c) :
    B.prefixWord side j = FlatAffineBranchPrefixChoice.value F cone height (B.sampleQuery side j) := by
  simp only [Family.prefixWord, Family.selectedWord, FlatAffineBranchPrefixChoice.value, Function.comp_apply,
    FlatAffineBranchChoice.parentRecord, Family.sampleQuery, FlatAffineEndpointBranchLabels.source, pairFst_pair]

theorem Family.prefixWord_valid (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (hold : (height (original c)).val < FlatAffineFullSourceTower.count F (original c))
    (side : Bool) (j : Index F cone height c) :
    SquareSampleCompleteVertices.Valid (FlatAffineJointPrefixChoice.target F cone height) (source c) (B.prefixWord side j) :=
  FlatAffineJointPrefixChoice.value_valid F cone height (source c) (B.selectedWord side j) hc.1 hold (B.selected_valid hc side j)

theorem Family.prefixWord_point (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (hold : (height (original c)).val < FlatAffineFullSourceTower.count F (original c))
    (side : Bool) (j : Index F cone height c) :
    (SquareSampleCompleteVertices.candidate (FlatAffineJointPrefixChoice.target F cone height) (source c)
      (B.prefixWord side j) (B.prefixWord_valid hc hold side j)).val =
      B.curve j (sampleValue F cone height side c) ∘
        FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
          (FlatAffineShiftPrefixInput.depth_le F height) (original c) := by
  have HW := B.selected_valid hc side j
  have HP := FlatAffineJointPrefixChoice.value_point F cone height (source c) (B.selectedWord side j) hc.1 hold HW
  have HC : FlatAffineEndpointFiniteProjection.copy F (source c)
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (source c) (B.selectedWord side j) HW).val 0 =
      FlatAffineEndpointRankWord.currentValue F cone height (source c) (B.selectedWord side j) :=
    (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F (source c) z 0)
      (FlatAffineEndpointRankWord.anchorPoint_packet F cone height (source c) (B.selectedWord side j) HW)).symm
  exact HP.trans (congrArg (fun f => f ∘ FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
    (FlatAffineShiftPrefixInput.depth_le F height) (original c)) (HC.trans (B.selected_current hc side j)))

theorem Family.prefixWord_same (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (hold : (height (original c)).val < FlatAffineFullSourceTower.count F (original c))
    (j : Index F cone height c) : B.prefixWord false j = B.prefixWord true j := by
  have HP := B.prefixWord_point hc hold false j
  have HQ := B.prefixWord_point hc hold true j
  have HE := B.frozen_prefix hold j
    ⟨sampleValue F cone height false c, Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between F cone height false c hc)⟩
    ⟨sampleValue F cone height true c, Ioo_subset_Icc_self (FlatAffineSlabGraphContext.samples_between F cone height true c hc)⟩
  exact SquareSampleCompleteVertices.candidate_injective (FlatAffineJointPrefixChoice.target F cone height) (source c)
    (B.prefixWord false j) (B.prefixWord true j) (B.prefixWord_valid hc hold false j) (B.prefixWord_valid hc hold true j)
    (Subtype.ext (HP.trans (HE.trans HQ.symm)))

theorem Family.native_prefix_same (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height)
    (hold : (height (original c)).val < FlatAffineFullSourceTower.count F (original c))
    (j : Index F cone height c) :
    FlatAffineBranchPrefixChoice.value F cone height (B.sampleQuery false j) =
      FlatAffineBranchPrefixChoice.value F cone height (B.sampleQuery true j) := by
  rw [← B.prefixWord_program false j, ← B.prefixWord_program true j]
  exact B.prefixWord_same hc hold j

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
