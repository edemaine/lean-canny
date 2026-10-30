/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineChildOriginalSamples

/-! # Native parent filtering for recursive child labels

The query pairs a child sample packet with an original parent word. Native
validation and computed-word comparison select exactly the children of that
decoded original parent, including its full multiplier tuple.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineChildParentMatch
open LeanCanny.Algebra LeanCanny.Computation
open CoordinateDoubleAffineChildRecords
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] CoordinateDoubleAffineChildRecords.parentWord
  SquareSampleCompleteVertices.Valid

noncomputable def language (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : Language :=
  {q | pairFst q ∈ SquareSampleCompleteVertices.language (childInput midpoint P depth old level) ∧
    parentWord midpoint P depth old level (pairFst q) = pairSnd q}

theorem decider (midpoint : Bool) {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceDecider (language midpoint P depth old level) := by
  have V := ((parentWord_evaluator midpoint hP hd ho hl hA).precompose pairFst pairFst_mem_FP).pairOutputs
    (SpaceFunction.ofFP pairSnd pairSnd_mem_FP)
  have E := V.postcompose (fun q => [decide (pairFst q = pairSnd q)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have D := ((SquareSampleCompleteVertices.decider
    (FlatAffinePowerSampleInput.access (access midpoint hP hd ho hl hA) (cone midpoint P depth old level))).precompose
      pairFst pairFst_mem_FP).flagEvaluator
  apply (D.andFlags E).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, Function.comp_apply,
    pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]
  rfl

theorem mem_PSPACE (midpoint : Bool) {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    language midpoint P depth old level ∈ PSPACE := (decider midpoint hP hd ho hl hA).mem_PSPACE

theorem packet (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w v : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (childInput midpoint P depth old level) u w)
    (hv : SquareSampleCompleteVertices.Valid (parentInput P depth old level) u v) :
    pair (pair u w) v ∈ language midpoint P depth old level ↔
      parent midpoint P depth old level u
          (FlatAffineCompleteVertices.vertexEquiv (inputs midpoint P depth old level) (cone midpoint P depth old level) u ⟨w, hw⟩) =
        FlatAffineCompleteVertices.vertexEquiv (CoordinateDoubleAffinePrefix.inputs P depth old level)
          (CoordinateDoubleAffinePrefix.coneCertificate P depth old level) u ⟨v, hv⟩ := by
  have hvalid : pair u w ∈ SquareSampleCompleteVertices.language (childInput midpoint P depth old level) := by
    simpa only [SquareSampleCompleteVertices.language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair] using hw
  simp only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, hvalid, true_and]
  constructor
  · intro he
    subst v
    exact (parentWord_root midpoint P depth old level u w hw).symm
  · intro he
    have H := (FlatAffineCompleteVertices.vertexEquiv (CoordinateDoubleAffinePrefix.inputs P depth old level)
      (CoordinateDoubleAffinePrefix.coneCertificate P depth old level) u).injective
        ((parentWord_root midpoint P depth old level u w hw).trans he)
    exact congrArg Subtype.val H

end LeanCanny.Encoding.CoordinateDoubleAffineChildParentMatch
