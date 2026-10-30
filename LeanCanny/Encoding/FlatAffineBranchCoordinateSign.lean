/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineBranchChoice
public import LeanCanny.Encoding.SquareSampleCompleteCoordinateSign

/-! # Native coordinate signs from short branch descriptors

The input pairs a validated branch query with one spatial coordinate index.
The native witness search and complete-root sign computation are both charged.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineBranchCoordinateSign
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointBranchLabels (source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def prepare (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) : List Bool :=
  pair (pair (source (pairFst r)) (FlatAffineBranchChoice.value F cone height (pairFst r)))
    (FlatAffineEndpointCopyEquality.slotWord F 0 (source (pairFst r)) (pairSnd r))

theorem prepareEvaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (prepare F cone height) := by
  have S := mem_FP_comp (f := pairFst) (g := source) pairFst_mem_FP FlatAffineEndpointBranchLabels.source_FP
  have Q := mem_FP_pair S pairSnd_mem_FP
  have P := (FlatAffineEndpointCopyEquality.slotWord_FP h 0)
  have W := (FlatAffineBranchChoice.evaluator h cone height hh).precompose pairFst pairFst_mem_FP
  have C := mem_FP_comp Q P
  exact ((SpaceFunction.ofFP _ S).pairOutputs W).pairOutputs
    ((SpaceFunction.ofFP _ C).congr (funext fun r => by simp only [Function.comp_apply, pairFst_pair, pairSnd_pair]))

theorem prepare_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q d : List Bool) :
    prepare F cone height (pair q d) = pair (pair (source q) (FlatAffineBranchChoice.value F cone height q))
      (FlatAffineEndpointCopyEquality.slotWord F 0 (source q) d) := by
  simp only [prepare, pairFst_pair, pairSnd_pair]

noncomputable def value (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : List Bool → List Bool :=
  SquareSampleCompleteCoordinateSign.value (FlatAffineEndpointFiniteSample.input F cone height) ∘ prepare F cone height

theorem evaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (value F cone height) :=
  (prepareEvaluator h cone height hh).chain
    (SquareSampleCompleteCoordinateSign.evaluator (FlatAffineEndpointFiniteSample.sampleAccess h cone height hh))

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointBranchLabels.language F cone height)
    (i : Fin (FlatAffineEndpointFiniteSide.originalCount F (source q))) :
    value F cone height (pair q (BinaryNatCode.encode i.val)) = InfinitesimalSign.encode (SignType.sign
      (FlatAffineEndpointRankWord.currentValue F cone height (source q) (FlatAffineBranchChoice.value F cone height q) i)) := by
  simp only [value, Function.comp_apply, prepare_packet, FlatAffineEndpointCopyEquality.slotWord,
    FlatAffineEndpointFiniteSide.coordinate_encode]
  rw [SquareSampleCompleteCoordinateSign.packet _ _ _ (FlatAffineBranchChoice.joint_valid F cone height q hq)]
  exact congrArg (fun x : ℝ => InfinitesimalSign.encode (SignType.sign x))
    (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F (source q) z 0 i)
      (FlatAffineEndpointRankWord.anchorPoint_packet F cone height (source q) (FlatAffineBranchChoice.value F cone height q)
        (FlatAffineBranchChoice.joint_valid F cone height q hq))).symm

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (sigma : SignType) : Language :=
  {r | pairFst r ∈ FlatAffineEndpointBranchLabels.language F cone height ∧ value F cone height r = InfinitesimalSign.encode sigma}

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (sigma : SignType) :
    SpaceDecider (language F cone height sigma) := by
  have V := ((FlatAffineEndpointBranchLabels.decider h cone height hh).precompose pairFst pairFst_mem_FP).flagEvaluator
  have E := (evaluator h cone height hh).postcompose (fun z => [decide (z = InfinitesimalSign.encode sigma)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP (InfinitesimalSign.encode sigma))).flag_mem_FP
  apply (V.andFlags E).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro r
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq, Function.comp_apply]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (sigma : SignType) :
    language F cone height sigma ∈ PSPACE := (decider h cone height hh sigma).mem_PSPACE

end LeanCanny.Encoding.FlatAffineBranchCoordinateSign
