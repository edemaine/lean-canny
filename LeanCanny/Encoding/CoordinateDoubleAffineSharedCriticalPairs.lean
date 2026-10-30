/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairParents

/-! # Native critical-pair filtering by exact shared ancestry

The paired label is validated before comparing its two computed original
parent words. Acceptance is exactly equality of the decoded original parents,
including all multiplier coordinates. No ancestry oracle is supplied.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] parentWord memberWord SquareSampleCompleteVertices.Valid

noncomputable def parentRoot (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (right : Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w) :=
  FlatAffineCompleteRootStages.project
    (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs P depth old level)) depth u
    (prefix_le P depth old level u) (memberRoot P depth old level right u w hw)

noncomputable def sharedLanguage (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : Language :=
  {q | q ∈ SquareSampleCompleteVertices.language (input P depth old level) ∧
    parentWord P depth old level false q = parentWord P depth old level true q}

theorem sharedDecider {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceDecider (sharedLanguage P depth old level) := by
  have W := (parentWord_evaluator hP hd ho hl hA false).pairOutputs (parentWord_evaluator hP hd ho hl hA true)
  have E := W.postcompose (fun q => [decide (LeanCanny.pairFst q = LeanCanny.pairSnd q)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have D := (SquareSampleCompleteVertices.decider (access hP hd ho hl hA)).flagEvaluator
  apply (D.andFlags E).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [sharedLanguage, Set.mem_ofPred_eq, Function.comp_apply, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem shared_mem_PSPACE {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    sharedLanguage P depth old level ∈ PSPACE := (sharedDecider hP hd ho hl hA).mem_PSPACE

theorem shared_packet (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input P depth old level) u w) :
    LeanCanny.pair u w ∈ sharedLanguage P depth old level ↔
      parentRoot P depth old level false u w hw = parentRoot P depth old level true u w hw := by
  have hvalid : LeanCanny.pair u w ∈ SquareSampleCompleteVertices.language (input P depth old level) := by
    simpa only [SquareSampleCompleteVertices.language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair] using hw
  simp only [sharedLanguage, Set.mem_ofPred_eq, hvalid, true_and]
  have HL := parentWord_root P depth old level false u w hw
  have HR := parentWord_root P depth old level true u w hw
  let e := FlatAffineCompleteVertices.vertexEquiv (CoordinateDoubleAffinePrefix.inputs P depth old level)
    (CoordinateDoubleAffinePrefix.coneCertificate P depth old level) u
  constructor
  · intro he
    have HE : (⟨parentWord P depth old level false (LeanCanny.pair u w), parentWord_valid P depth old level false u w hw⟩ :
        {v // FlatAffineCompleteVertices.Valid (CoordinateDoubleAffinePrefix.inputs P depth old level)
          (CoordinateDoubleAffinePrefix.coneCertificate P depth old level) u v}) =
      ⟨parentWord P depth old level true (LeanCanny.pair u w), parentWord_valid P depth old level true u w hw⟩ :=
      Subtype.ext he
    exact HL.symm.trans ((congrArg e HE).trans HR)
  · intro he
    have H := e.injective (HL.trans (he.trans HR.symm))
    exact congrArg Subtype.val H

end LeanCanny.Encoding.CoordinateDoubleAffineCriticalPairs
