/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteVertices
public import LeanCanny.Encoding.SquareSamplePolynomialTest

/-! # Native polynomial signs at all square-system vertices

The regular grid sampler and the original system use the same primitive
parameter. Polynomial test signs therefore work at complete vertex labels,
including singular roots of the original equations. The native language
checks the original equations and rejects malformed labels.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompletePolynomialTest
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def value (F : Inputs) (T : SquareSamplePolynomialTest.Test F) : List Bool → List Bool :=
  SquareSampleCompleteVertices.signValue F (SquareSamplePolynomialTest.test T)

theorem evaluator {F : Inputs} (h : F.Access) {T : SquareSamplePolynomialTest.Test F} (A : T.Access) :
    SpaceFunction (value F T) :=
  SquareSampleCompleteVertices.sign_evaluator h (SquareSamplePolynomialTest.test_access h A)

theorem packet (F : Inputs) (T : SquareSamplePolynomialTest.Test F) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F u w) : value F T (pair u w) = InfinitesimalSign.encode
      (SignType.sign ((T.polynomial u).eval₂ (Int.castRingHom ℝ)
        (SquareSampleCompleteVertices.candidate F u w hw).val)) := by
  rw [value, SquareSampleCompleteVertices.sign_packet F (SquareSamplePolynomialTest.test T) u w hw]
  have ht := (SquareSampleQueries.mem_roots (SquareSampleGrid.input F) u
    (SquareSampleCompleteVertices.theta F u w (Classical.choose hw)).val).mp
      (SquareSampleCompleteVertices.theta F u w (Classical.choose hw)).property
  rw [SquareSampleGrid.parameter_eq] at ht
  rw [SquareSamplePolynomialTest.sign F T u _ ht.1]
  rfl

noncomputable def language (F : Inputs) (T : SquareSamplePolynomialTest.Test F) (s : SignType) : Language :=
  {q | SquareSampleCompleteVertices.Valid F (pairFst q) (pairSnd q) ∧ value F T q = InfinitesimalSign.encode s}

theorem decider {F : Inputs} (h : F.Access) {T : SquareSamplePolynomialTest.Test F} (A : T.Access) (s : SignType) :
    SpaceDecider (language F T s) := by
  have V := (SquareSampleCompleteVertices.decider h).flagEvaluator
  have E := V.pairOutputs (evaluator h A)
  apply E.decider (fun q => decide (pairFst q = [true] ∧ pairSnd q = InfinitesimalSign.encode s))
    ((Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).and
      (Brackets.stringEq_fppred pairSnd_mem_FP (constFn_mem_FP _))).flag_mem_FP
  intro q
  simp only [language, SquareSampleCompleteVertices.language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) {T : SquareSamplePolynomialTest.Test F} (A : T.Access) (s : SignType) :
    language F T s ∈ PSPACE := (decider h A s).mem_PSPACE

theorem language_packet (F : Inputs) (T : SquareSamplePolynomialTest.Test F) (s : SignType) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F u w) : pair u w ∈ language F T s ↔
      SignType.sign ((T.polynomial u).eval₂ (Int.castRingHom ℝ)
        (SquareSampleCompleteVertices.candidate F u w hw).val) = s := by
  simp only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, hw, true_and, packet F T u w hw]
  exact SquareSampleTestSign.encode_eq_iff _ _

end LeanCanny.Encoding.SquareSampleCompletePolynomialTest
