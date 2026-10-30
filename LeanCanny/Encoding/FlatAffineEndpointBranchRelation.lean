/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointBranchLabels

/-! # Native branch comparison with checked original-slab identities

Two joint roots, their independent scalar sample labels, and a shared binary
slab code are checked before their persistent rank descriptors are compared.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointBranchRelation
open LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def source (q : List Bool) : List Bool := pairFst (pairFst q)
def gapWord (q : List Bool) : List Bool := pairSnd (pairFst q)
def leftRecord (q : List Bool) : List Bool := pairFst (pairSnd q)
def rightRecord (q : List Bool) : List Bool := pairSnd (pairSnd q)
def slabQuery (right : Bool) (q : List Bool) : List Bool :=
  let r := if right then rightRecord q else leftRecord q
  pair (pair (source q) (pairFst r)) (pair (pairSnd r) (gapWord q))
def equalityQuery (q : List Bool) : List Bool :=
  pair (source q) (pair (pairFst (leftRecord q)) (pairFst (rightRecord q)))
theorem slabQuery_FP (right : Bool) : slabQuery right ∈ FP := by
  cases right <;> polytime [slabQuery, source, gapWord, leftRecord, rightRecord]
theorem equalityQuery_FP : equalityQuery ∈ FP := by polytime [equalityQuery, source, leftRecord, rightRecord]

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {q | slabQuery false q ∈ FlatAffineEndpointSampleSlab.language F cone height ∧
    slabQuery true q ∈ FlatAffineEndpointSampleSlab.language F cone height ∧
    equalityQuery q ∈ FlatAffineEndpointRankWordEquality.language F cone height}

attribute [local irreducible] FlatAffineEndpointSampleSlab.language FlatAffineEndpointRankWordEquality.language

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider (language F cone height) := by
  have S := FlatAffineEndpointSampleSlab.decider h cone height hh
  have L := (S.precompose (slabQuery false) (slabQuery_FP false)).flagEvaluator
  have R := (S.precompose (slabQuery true) (slabQuery_FP true)).flagEvaluator
  have E := ((FlatAffineEndpointRankWordEquality.decider h cone height hh).precompose equalityQuery equalityQuery_FP).flagEvaluator
  apply (L.andFlags (R.andFlags E)).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    language F cone height ∈ PSPACE := (decider h cone height hh).mem_PSPACE

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w v tWord uWord kWord : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (hW : pair (pair s w) (pair tWord kWord) ∈ FlatAffineEndpointSampleSlab.language F cone height)
    (hV : pair (pair s v) (pair uWord kWord) ∈ FlatAffineEndpointSampleSlab.language F cone height) :
    pair (pair s kWord) (pair (pair w tWord) (pair v uWord)) ∈ language F cone height ↔
      FlatAffineEndpointRankWord.word F cone height (pair s w) = FlatAffineEndpointRankWord.word F cone height (pair s v) := by
  simp only [language, Set.mem_ofPred_eq, slabQuery, source, gapWord, leftRecord, rightRecord, equalityQuery,
    Bool.false_eq_true, ite_false, ite_true, pairFst_pair, pairSnd_pair, hW, hV, true_and]
  exact FlatAffineEndpointRankWordEquality.packet F cone height s w v hs hw hv

end LeanCanny.Encoding.FlatAffineEndpointBranchRelation
