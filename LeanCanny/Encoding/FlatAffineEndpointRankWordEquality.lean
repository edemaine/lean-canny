/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointRankWordPersistence

/-! # Native equality of valid joint-sample rank descriptors

The source frame and both complete joint labels are checked before comparing
their descriptors. On one retained interval, the geometric identification
theorem makes this exactly equality of the denoted branches.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointRankWordEquality
open LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def left (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd q))
def right (q : List Bool) : List Bool := pair (pairFst q) (pairSnd (pairSnd q))
theorem left_FP : left ∈ FP := by polytime [left]
theorem right_FP : right ∈ FP := by polytime [right]

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {q | left q ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) ∧
    right q ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) ∧
    FlatAffineEndpointRankWord.word F cone height (left q) = FlatAffineEndpointRankWord.word F cone height (right q)}

attribute [local irreducible] FlatAffineEndpointRankWord.word GuardedSquareSampleInput.language

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider (language F cone height) := by
  have D := GuardedSquareSampleInput.decider (FlatAffineEndpointFiniteSample.access h cone height hh)
  have L := (D.precompose left left_FP).flagEvaluator
  have R := (D.precompose right right_FP).flagEvaluator
  have W := FlatAffineEndpointRankWord.evaluator h cone height hh
  have E := ((W.precompose left left_FP).pairOutputs (W.precompose right right_FP)).postcompose
    (fun z => [decide (pairFst z = pairSnd z)]) (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  apply (L.andFlags (R.andFlags E)).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    language F cone height ∈ PSPACE := (decider h cone height hh).mem_PSPACE

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w v : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v) :
    pair s (pair w v) ∈ language F cone height ↔
      FlatAffineEndpointRankWord.word F cone height (pair s w) = FlatAffineEndpointRankWord.word F cone height (pair s v) := by
  have good (a : List Bool) (ha : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s a) :
      pair s a ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) := by
    unfold GuardedSquareSampleInput.language
    change pairFst (pair s a) ∈ (FlatAffineEndpointFiniteSample.data F cone height).good ∧
      SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (pairFst (pair s a)) (pairSnd (pair s a))
    rw [pairFst_pair, pairSnd_pair]
    exact ⟨hs, ha⟩
  simp only [language, Set.mem_ofPred_eq, left, right, pairFst_pair, pairSnd_pair, good w hw, good v hv, true_and]

end LeanCanny.Encoding.FlatAffineEndpointRankWordEquality
