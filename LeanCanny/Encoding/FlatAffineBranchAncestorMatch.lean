/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineBranchPrefixChoice

/-! # Native exact-ancestor filtering of short branch descriptors

The query pairs a native branch descriptor with a complete frozen ancestor
word. The program validates the descriptor, computes its ancestor word, and
compares the two words. No ancestor comparison oracle is supplied.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineBranchAncestorMatch
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointBranchLabels (source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineBranchPrefixChoice.value FlatAffineBranchChoice.value
  FlatAffineEndpointBranchLabels.language FlatAffineJointPrefixChoice.value

noncomputable def language (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {q | pairFst q ∈ FlatAffineEndpointBranchLabels.language F C height ∧
    FlatAffineBranchPrefixChoice.value F C height (pairFst q) = pairSnd q}

theorem decider {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceDecider (language F C height) := by
  have V := ((FlatAffineBranchPrefixChoice.evaluator hF C height hh).precompose pairFst pairFst_mem_FP).pairOutputs
    (SpaceFunction.ofFP pairSnd pairSnd_mem_FP)
  have E := V.postcompose (fun q => [decide (pairFst q = pairSnd q)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have D := ((FlatAffineEndpointBranchLabels.decider hF C height hh).precompose pairFst pairFst_mem_FP).flagEvaluator
  apply (D.andFlags E).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    language F C height ∈ PSPACE := (decider hF C height hh).mem_PSPACE

theorem packet (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q v : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language F C height)
    (hold : (height (FlatAffineJointPrefixChoice.original (source q))).val <
      FlatAffineFullSourceTower.count F (FlatAffineJointPrefixChoice.original (source q)))
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineJointPrefixChoice.target F C height) (source q) v) :
    pair q v ∈ language F C height ↔
      (SquareSampleCompleteVertices.candidate (FlatAffineJointPrefixChoice.target F C height) (source q) v hv).val =
        FlatAffineEndpointRankWord.currentValue F C height (source q) (FlatAffineBranchChoice.value F C height q) ∘
          FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
            (FlatAffineShiftPrefixInput.depth_le F height) (FlatAffineJointPrefixChoice.original (source q)) := by
  have HW := FlatAffineBranchPrefixChoice.value_valid F C height q hq hold
  have HP := FlatAffineBranchPrefixChoice.value_point F C height q hq hold
  simp only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair]
  constructor
  · rintro ⟨_, he⟩
    subst v
    exact HP
  · intro he
    refine ⟨hq, SquareSampleCompleteVertices.candidate_injective _ _ _ _ HW hv ?_⟩
    exact Subtype.ext (HP.trans he.symm)

end LeanCanny.Encoding.FlatAffineBranchAncestorMatch
