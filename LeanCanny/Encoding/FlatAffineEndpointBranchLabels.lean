/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointRankWordEquality
public import LeanCanny.Encoding.FlatAffineEndpointSampleSlab
public import LeanCanny.Computation.SpaceFunctionWordExistence

/-! # Native short branch labels at a checked original-slab sample

The input stores the frame, scalar sample label, original gap code, and rank
descriptor. A bounded native search validates an actual joint root with that
sample and descriptor. Exponential witness enumeration uses polynomial space.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointBranchLabels
open LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def source (q : List Bool) : List Bool := pairFst (pairFst q)
def samplePacket (q : List Bool) : List Bool := pairSnd (pairFst q)
def descriptor (q : List Bool) : List Bool := pairSnd q
theorem source_FP : source ∈ FP := by polytime [source]
def candidateQuery (r : List Bool) : List Bool := pair (source (pairFst r)) (pairSnd r)
def slabQuery (r : List Bool) : List Bool := pair (candidateQuery r) (samplePacket (pairFst r))
def targetQuery (r : List Bool) : List Bool := descriptor (pairFst r)
theorem candidateQuery_FP : candidateQuery ∈ FP := by polytime [candidateQuery, source]
theorem slabQuery_FP : slabQuery ∈ FP := by polytime [slabQuery, candidateQuery, source, samplePacket]
theorem targetQuery_FP : targetQuery ∈ FP := by polytime [targetQuery, descriptor]

noncomputable def test (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) : List Bool :=
  [decide (slabQuery r ∈ FlatAffineEndpointSampleSlab.language F cone height ∧
    FlatAffineEndpointRankWord.word F cone height (candidateQuery r) = targetQuery r)]

attribute [local irreducible] FlatAffineEndpointSampleSlab.language FlatAffineEndpointRankWord.word

theorem testEvaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (test F cone height) := by
  have S := ((FlatAffineEndpointSampleSlab.decider h cone height hh).precompose slabQuery slabQuery_FP).flagEvaluator
  have W := (FlatAffineEndpointRankWord.evaluator h cone height hh).precompose candidateQuery candidateQuery_FP
  have T := SpaceFunction.ofFP targetQuery targetQuery_FP
  have E := (W.pairOutputs T).postcompose (fun z => [decide (pairFst z = pairSnd z)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  exact (S.andFlags E).congr (funext fun r => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Set.mem_preimage, Function.comp_apply, pairFst_pair, pairSnd_pair,
      List.cons.injEq, and_true, decide_eq_true_eq])

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {q | ∃ w : List Bool, w.length = SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) (source q) ∧
    slabQuery (pair q w) ∈ FlatAffineEndpointSampleSlab.language F cone height ∧
      FlatAffineEndpointRankWord.word F cone height (candidateQuery (pair q w)) = descriptor q}

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider (language F cone height) := by
  have E := (testEvaluator h cone height hh).exists_words ((FlatAffineEndpointFiniteSample.width_unary h cone height hh).comp source_FP)
  apply E.decider (fun z => decide (z = [true])) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, test, pairFst_pair, targetQuery, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    language F cone height ∈ PSPACE := (decider h cone height hh).mem_PSPACE

theorem witness (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q w : List Bool)
    (hq : slabQuery (pair q w) ∈ FlatAffineEndpointSampleSlab.language F cone height)
    (he : FlatAffineEndpointRankWord.word F cone height (candidateQuery (pair q w)) = descriptor q) :
    q ∈ language F cone height := by
  have hw := FlatAffineEndpointSampleSlab.joint_valid F cone height _ hq
  have H := (Classical.choose hw).1
  have hlen : w.length = SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) (source q) := by
    simpa only [slabQuery, candidateQuery, pairFst_pair, pairSnd_pair, SquareSampleCompleteVertices.width] using H
  exact ⟨w, hlen, hq, he⟩

theorem valid_length (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) (hq : q ∈ language F cone height) :
    (descriptor q).length = FlatAffineEndpointFiniteSide.originalCount F (source q) *
      (SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) (source q) + 1) := by
  obtain ⟨w, _, _, he⟩ := hq
  rw [← he, FlatAffineEndpointRankWord.word_length]
  simp only [candidateQuery, pairFst_pair, FlatAffineEndpointRankWord.arity, FlatAffineEndpointRankWord.width]

end LeanCanny.Encoding.FlatAffineEndpointBranchLabels
