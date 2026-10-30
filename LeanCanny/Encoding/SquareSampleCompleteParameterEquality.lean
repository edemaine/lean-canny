/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteParameterTest
public import LeanCanny.Algebra.IntegerPolynomialIteratedDerivativeSource
public import LeanCanny.Algebra.ThomEncoding
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers

/-! # Binding a complete point's primitive parameter to a scalar root label

Both samplers keep their original source. A binary scan compares all Thom
signs of the common primitive polynomial. This validates an exact scalar
record for a parent point; neither a separating linear form nor numerical
coordinates are required as extra input.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteParameterEquality
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open SquareSampleCompleteParameterTest (source theta)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def origin (q : List Bool) : List Bool := pairFst (pairFst q)
def scalarVertex (q : List Bool) : List Bool := pair (origin q) (pairSnd q)
def jointProbe (r : List Bool) : List Bool := pair (pairFst (pairFst r)) (pairSnd r)
def scalarProbe (r : List Bool) : List Bool := pair (scalarVertex (pairFst r)) (pairSnd r)
theorem origin_FP : origin ∈ FP := by polytime [origin]
theorem scalarVertex_FP : scalarVertex ∈ FP := by polytime [scalarVertex, origin]
theorem jointProbe_FP : jointProbe ∈ FP := by polytime [jointProbe]
theorem scalarProbe_FP : scalarProbe ∈ FP := by polytime [scalarProbe, scalarVertex, origin]

noncomputable def agrees (F : Inputs) (q : List Bool) : Prop :=
  ∀ k < (source F).degree (origin q) + 1,
    SquareSampleCompleteParameterTest.value F (IntegerPolynomialIteratedDerivativeBits.source (source F))
      (jointProbe (pair q (BinaryNatCode.encode k))) =
    IntegerPolynomialIndexedSampleTest.value (source F) (IntegerPolynomialIteratedDerivativeBits.source (source F))
      (scalarProbe (pair q (BinaryNatCode.encode k)))

noncomputable def language (F : Inputs) : Language :=
  {q | SquareSampleCompleteVertices.Valid F (origin q) (pairSnd (pairFst q)) ∧
    scalarVertex q ∈ SquareSampleCompleteVertices.language (IntegerPolynomialSampleInput.input (source F)) ∧ agrees F q}

section native
attribute [local irreducible] SquareSampleCompleteParameterTest.value IntegerPolynomialIndexedSampleTest.value
  SquareSampleCompleteVertices.language

theorem scanEvaluator {F : Inputs} (h : F.Access) : SpaceFunction (fun q => [decide (agrees F q)]) := by
  have A := SquareSampleCompleteParameterTest.sourceAccess h
  have D := IntegerPolynomialIteratedDerivativeBits.access A
  have J := (SquareSampleCompleteParameterTest.evaluator h D).precompose jointProbe jointProbe_FP
  have R := (IntegerPolynomialIndexedSampleTest.evaluator A D).precompose scalarProbe scalarProbe_FP
  have E := (J.pairOutputs R).postcompose (fun z => [decide (pairFst z = pairSnd z)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have N : BinaryFn (fun q => (source F).degree (origin q)) := A.degree.comp origin_FP
  exact (E.forall_binary (N.add (BinaryFn.const 1))).congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [agrees, Function.comp_apply, pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq])

theorem decider {F : Inputs} (h : F.Access) : SpaceDecider (language F) := by
  have J := ((SquareSampleCompleteVertices.decider h).precompose pairFst pairFst_mem_FP).flagEvaluator
  have R := ((SquareSampleCompleteVertices.decider (IntegerPolynomialSampleInput.access
    (SquareSampleCompleteParameterTest.sourceAccess h))).precompose scalarVertex scalarVertex_FP).flagEvaluator
  apply (J.andFlags (R.andFlags (scanEvaluator h))).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, SquareSampleCompleteVertices.language, origin,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) : language F ∈ PSPACE := (decider h).mem_PSPACE

end native

theorem packet (F : Inputs) (c w v : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w)
    (hv : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (source F)) c v) :
    pair (pair c w) v ∈ language F ↔ theta F c w =
      (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input (source F)) c v hv).val (0 : Fin 1) := by
  have HJ (k : ℕ) := SquareSampleCompleteParameterTest.packet F (IntegerPolynomialIteratedDerivativeBits.source (source F))
    c w (BinaryNatCode.encode k) hw
  have HR (k : ℕ) := IntegerPolynomialIndexedSampleTest.packet (source F) (IntegerPolynomialIteratedDerivativeBits.source (source F))
    c v (BinaryNatCode.encode k) hv
  simp only [language, Set.mem_ofPred_eq, origin, scalarVertex, pairFst_pair, pairSnd_pair,
    SquareSampleCompleteVertices.language, hw, hv, true_and, agrees, jointProbe, scalarProbe]
  simp_rw [HJ, HR, IntegerPolynomialIteratedDerivativeBits.packet, SquareSampleTestSign.encode_eq_iff]
  constructor
  · intro hs
    apply ThomEncoding.root_eq (((source F).polynomial c).map (Int.castRingHom ℝ))
      ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr (SquareSampleCoordinates.parameter_ne_zero F c))
      ((source F).degree c) (Polynomial.natDegree_map_le.trans ((source F).degree_bound c))
    · rw [Polynomial.eval_map]
      exact SquareSampleCompleteParameterTest.theta_root F c w hw
    · rw [Polynomial.eval_map]
      exact (IntegerPolynomialSampleInput.roots_iff (source F) c (SquareSampleCoordinates.parameter_ne_zero F c) _).mp
        (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input (source F)) c v hv).property
    · intro k hk
      simpa only [ThomEncoding.sign, Polynomial.iterate_derivative_map, Polynomial.eval_map] using hs k (by omega)
  · intro he k _
    simp only [he]

theorem label_exists (F : Inputs) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    ∃ v, pair (pair c w) v ∈ language F := by
  obtain ⟨v, hv, he⟩ := IntegerPolynomialSampleInput.root_complete (source F) c
    (SquareSampleCoordinates.parameter_ne_zero F c) (theta F c w) (SquareSampleCompleteParameterTest.theta_root F c w hw)
  exact ⟨v, (packet F c w v hw hv).mpr he.symm⟩

end LeanCanny.Encoding.SquareSampleCompleteParameterEquality
