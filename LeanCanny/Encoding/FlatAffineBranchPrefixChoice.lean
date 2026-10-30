/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineJointPrefixChoice
public import LeanCanny.Encoding.FlatAffineBranchChoice

/-! # Computing frozen ancestor labels from native branch descriptors

The branch's native witness search supplies a complete current sample. The
joint-prefix routine then computes its exact complete frozen ancestor label.
Both searches and all original coefficient readers are charged.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineBranchPrefixChoice
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointBranchLabels (source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

noncomputable def value (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : List Bool → List Bool :=
  FlatAffineJointPrefixChoice.value F C height ∘ FlatAffineBranchChoice.parentRecord F C height

theorem evaluator {F : Inputs} (h : F.Access) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (value F C height) :=
  (FlatAffineBranchChoice.parentEvaluator h C height hh).chain (FlatAffineJointPrefixChoice.evaluator h C height hh)

theorem value_valid (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language F C height)
    (hold : (height (FlatAffineJointPrefixChoice.original (source q))).val <
      FlatAffineFullSourceTower.count F (FlatAffineJointPrefixChoice.original (source q))) :
    SquareSampleCompleteVertices.Valid (FlatAffineJointPrefixChoice.target F C height) (source q) (value F C height q) :=
  FlatAffineJointPrefixChoice.value_valid F C height (source q) (FlatAffineBranchChoice.value F C height q)
    (FlatAffineBranchChoice.frame_valid F C height q hq) hold (FlatAffineBranchChoice.joint_valid F C height q hq)

theorem value_point (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language F C height)
    (hold : (height (FlatAffineJointPrefixChoice.original (source q))).val <
      FlatAffineFullSourceTower.count F (FlatAffineJointPrefixChoice.original (source q))) :
    (SquareSampleCompleteVertices.candidate (FlatAffineJointPrefixChoice.target F C height) (source q)
      (value F C height q) (value_valid F C height q hq hold)).val =
      FlatAffineEndpointRankWord.currentValue F C height (source q) (FlatAffineBranchChoice.value F C height q) ∘
        FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height) (FlatAffineShiftPrefixInput.depth_le F height)
          (FlatAffineJointPrefixChoice.original (source q)) := by
  have HW := FlatAffineBranchChoice.joint_valid F C height q hq
  have HP := FlatAffineJointPrefixChoice.value_point F C height (source q) (FlatAffineBranchChoice.value F C height q)
    (FlatAffineBranchChoice.frame_valid F C height q hq) hold HW
  have HC : FlatAffineEndpointFiniteProjection.copy F (source q)
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F C height) (source q)
        (FlatAffineBranchChoice.value F C height q) HW).val 0 =
    FlatAffineEndpointRankWord.currentValue F C height (source q) (FlatAffineBranchChoice.value F C height q) :=
    (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F (source q) z 0)
      (FlatAffineEndpointRankWord.anchorPoint_packet F C height (source q) (FlatAffineBranchChoice.value F C height q) HW)).symm
  exact HP.trans (congrArg (fun f => f ∘ FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
    (FlatAffineShiftPrefixInput.depth_le F height) (FlatAffineJointPrefixChoice.original (source q))) HC)

end LeanCanny.Encoding.FlatAffineBranchPrefixChoice
