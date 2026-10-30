/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineJointCopyPrefixChoice
public import LeanCanny.Encoding.FlatAffineEndpointMarkers

/-! # Native endpoint markers select their own exact frozen ancestors

The marker's first endpoint copy supplies its parent. Auxiliary current and
other endpoint copies are not used to determine this ancestor.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointAncestorMatch
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointMarkers (source jointWord jointQuery jointQuery_FP)
open FlatAffineJointPrefixChoice (target)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] FlatAffineJointCopyPrefixChoice.value FlatAffineEndpointMarkers.language

noncomputable def value (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : List Bool → List Bool :=
  FlatAffineJointCopyPrefixChoice.value F C height 1 ∘ jointQuery

theorem evaluator {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (value F C height) :=
  (FlatAffineJointCopyPrefixChoice.evaluator hF C height hh 1).precompose jointQuery jointQuery_FP

noncomputable def language (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {q | pairFst q ∈ FlatAffineEndpointMarkers.language F C height ∧ value F C height (pairFst q) = pairSnd q}

theorem decider {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider (language F C height) := by
  have V := ((evaluator hF C height hh).precompose pairFst pairFst_mem_FP).pairOutputs
    (SpaceFunction.ofFP pairSnd pairSnd_mem_FP)
  have E := V.postcompose (fun q => [decide (pairFst q = pairSnd q)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have D := ((FlatAffineEndpointMarkers.decider hF C height hh).precompose pairFst pairFst_mem_FP).flagEvaluator
  apply (D.andFlags E).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : language F C height ∈ PSPACE :=
  (decider hF C height hh).mem_PSPACE

theorem value_valid (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language F C height)
    (hold : (height (FlatAffineJointPrefixChoice.original (source q))).val <
      FlatAffineFullSourceTower.count F (FlatAffineJointPrefixChoice.original (source q))) :
    SquareSampleCompleteVertices.Valid (target F C height) (source q) (value F C height q) :=
  FlatAffineJointCopyPrefixChoice.value_valid F C height 1 (source q) (jointWord q)
    (FlatAffineEndpointMarkers.frame_valid F C height q hq) hold (FlatAffineEndpointMarkers.joint_valid F C height q hq)

theorem packet (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q v : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language F C height)
    (hold : (height (FlatAffineJointPrefixChoice.original (source q))).val <
      FlatAffineFullSourceTower.count F (FlatAffineJointPrefixChoice.original (source q)))
    (hv : SquareSampleCompleteVertices.Valid (target F C height) (source q) v) :
    pair q v ∈ language F C height ↔
      (SquareSampleCompleteVertices.candidate (target F C height) (source q) v hv).val =
        FlatAffineEndpointFiniteProjection.copy F (source q)
          (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F C height) (source q)
            (jointWord q) (FlatAffineEndpointMarkers.joint_valid F C height q hq)).val 1 ∘
          FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
            (FlatAffineShiftPrefixInput.depth_le F height) (FlatAffineJointPrefixChoice.original (source q)) := by
  have HW := value_valid F C height q hq hold
  have HP := FlatAffineJointCopyPrefixChoice.value_point F C height 1 (source q) (jointWord q)
    (FlatAffineEndpointMarkers.frame_valid F C height q hq) hold (FlatAffineEndpointMarkers.joint_valid F C height q hq)
  simp only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, hq, true_and]
  constructor
  · intro he
    subst v
    exact HP
  · intro he
    exact SquareSampleCompleteVertices.candidate_injective _ _ _ _ HW hv (Subtype.ext (HP.trans he.symm))

end LeanCanny.Encoding.FlatAffineEndpointAncestorMatch
