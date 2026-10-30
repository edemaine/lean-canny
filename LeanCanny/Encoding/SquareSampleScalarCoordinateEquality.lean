/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteUnivariateTest
public import LeanCanny.Encoding.IntegerPolynomialIndexedSampleTest
public import LeanCanny.Algebra.IntegerPolynomialIteratedDerivativeSource
public import LeanCanny.Algebra.ThomEncoding
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers

/-! # A joint coordinate compared with an independently labeled scalar root

The scalar sampler keeps its original source record. Binary derivative
probes pull that source back to the joint record and preserve both labels.
Agreement of all probes is exactly equality of the two algebraic values.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleScalarCoordinateEquality
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open IntegerPolynomialRootQueriesBits (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def source (q : List Bool) : List Bool := pairFst (pairFst q)
theorem source_FP : source ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
def scalarVertex (f : List Bool → List Bool) (q : List Bool) : List Bool := pair (f (source q)) (pairSnd q)
theorem scalarVertex_FP {f : List Bool → List Bool} (hf : f ∈ FP) : scalarVertex f ∈ FP :=
  mem_FP_pair (mem_FP_comp source_FP hf) pairSnd_mem_FP
def derivativeContext (f : List Bool → List Bool) (z : List Bool) : List Bool := pair (f (pairFst z)) (pairSnd z)
theorem derivativeContext_FP {f : List Bool → List Bool} (hf : f ∈ FP) : derivativeContext f ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP hf) pairSnd_mem_FP

noncomputable def jointSource (S : Source) (f : List Bool → List Bool) : Source :=
  IntegerPolynomialIteratedDerivativeBits.comp (IntegerPolynomialIteratedDerivativeBits.source S) (derivativeContext f)

noncomputable def jointValue (F : Inputs) (S : Source) (f : List Bool → List Bool)
    (coordinate : (c : List Bool) → Fin (F.count c)) : List Bool → List Bool :=
  SquareSampleCompleteUnivariateTest.value F (jointSource S f) (fun c _ => coordinate c)

def jointProbe (r : List Bool) : List Bool := pair (pairFst (pairFst r)) (pairSnd r)
def scalarProbe (f : List Bool → List Bool) (r : List Bool) : List Bool := pair (scalarVertex f (pairFst r)) (pairSnd r)
theorem jointProbe_FP : jointProbe ∈ FP := by polytime [jointProbe]
theorem scalarProbe_FP {f : List Bool → List Bool} (hf : f ∈ FP) : scalarProbe f ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP (scalarVertex_FP hf)) pairSnd_mem_FP

noncomputable def agrees (F : Inputs) (S : Source) (f : List Bool → List Bool)
    (coordinate : (c : List Bool) → Fin (F.count c)) (q : List Bool) : Prop :=
  ∀ k < S.degree (f (source q)) + 1,
    jointValue F S f coordinate (jointProbe (pair q (BinaryNatCode.encode k))) =
      IntegerPolynomialIndexedSampleTest.value S (IntegerPolynomialIteratedDerivativeBits.source S)
        (scalarProbe f (pair q (BinaryNatCode.encode k)))

noncomputable def language (F : Inputs) (S : Source) (f : List Bool → List Bool)
    (coordinate : (c : List Bool) → Fin (F.count c)) : Language :=
  {q | SquareSampleCompleteVertices.Valid F (source q) (pairSnd (pairFst q)) ∧
    scalarVertex f q ∈ SquareSampleCompleteVertices.language (IntegerPolynomialSampleInput.input S) ∧ agrees F S f coordinate q}

section native
attribute [local irreducible] jointValue IntegerPolynomialIndexedSampleTest.value SquareSampleCompleteVertices.language

theorem scanEvaluator {F : Inputs} (h : F.Access) {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    {f : List Bool → List Bool} (hf : f ∈ FP) (coordinate : (c : List Bool) → Fin (F.count c))
    (hi : UnaryFn (fun c => (coordinate c).val)) : SpaceFunction (fun q => [decide (agrees F S f coordinate q)]) := by
  have D := IntegerPolynomialIteratedDerivativeBits.access A
  have J := (SquareSampleCompleteUnivariateTest.evaluator h
    (IntegerPolynomialIteratedDerivativeBits.compAccess D (derivativeContext_FP hf))
    (fun c _ => coordinate c) (hi.comp pairFst_mem_FP)).precompose jointProbe jointProbe_FP
  have R := (IntegerPolynomialIndexedSampleTest.evaluator A D).precompose (scalarProbe f) (scalarProbe_FP hf)
  have E := (J.pairOutputs R).postcompose (fun z => [decide (pairFst z = pairSnd z)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have N : BinaryFn (fun q => S.degree (f (source q))) := A.degree.comp (mem_FP_comp source_FP hf)
  exact (E.forall_binary (N.add (BinaryFn.const 1))).congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [agrees, jointValue, jointSource, Function.comp_apply, pairFst_pair, pairSnd_pair,
      List.cons.injEq, and_true, decide_eq_true_eq])

theorem decider {F : Inputs} (h : F.Access) {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    {f : List Bool → List Bool} (hf : f ∈ FP) (coordinate : (c : List Bool) → Fin (F.count c))
    (hi : UnaryFn (fun c => (coordinate c).val)) : SpaceDecider (language F S f coordinate) := by
  have J := ((SquareSampleCompleteVertices.decider h).precompose pairFst pairFst_mem_FP).flagEvaluator
  have R := ((SquareSampleCompleteVertices.decider (IntegerPolynomialSampleInput.access A)).precompose
    (scalarVertex f) (scalarVertex_FP hf)).flagEvaluator
  apply (J.andFlags (R.andFlags (scanEvaluator h A hf coordinate hi))).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, SquareSampleCompleteVertices.language, source,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    {f : List Bool → List Bool} (hf : f ∈ FP) (coordinate : (c : List Bool) → Fin (F.count c))
    (hi : UnaryFn (fun c => (coordinate c).val)) : language F S f coordinate ∈ PSPACE :=
  (decider h A hf coordinate hi).mem_PSPACE

end native

theorem packet (F : Inputs) (S : Source) (f : List Bool → List Bool)
    (coordinate : (c : List Bool) → Fin (F.count c)) (c w v : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F c w)
    (hv : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input S) (f c) v)
    (hn : S.polynomial (f c) ≠ 0)
    (hr : (S.polynomial (f c)).eval₂ (Int.castRingHom ℝ) ((SquareSampleCompleteVertices.candidate F c w hw).val (coordinate c)) = 0) :
    pair (pair c w) v ∈ language F S f coordinate ↔
      (SquareSampleCompleteVertices.candidate F c w hw).val (coordinate c) =
        (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input S) (f c) v hv).val (0 : Fin 1) := by
  have hQ (k : ℕ) : (jointSource S f).polynomial (pair c (BinaryNatCode.encode k)) =
      Polynomial.derivative^[k] (S.polynomial (f c)) := by
    simp only [jointSource, IntegerPolynomialIteratedDerivativeBits.comp, Function.comp_apply,
      derivativeContext, pairFst_pair, pairSnd_pair]
    exact IntegerPolynomialIteratedDerivativeBits.packet S (f c) k
  have HJ (k : ℕ) : jointValue F S f coordinate (pair (pair c w) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (ThomEncoding.sign ((S.polynomial (f c)).map (Int.castRingHom ℝ))
        ((SquareSampleCompleteVertices.candidate F c w hw).val (coordinate c)) k) := by
    rw [jointValue, SquareSampleCompleteUnivariateTest.packet _ _ _ c w _ hw, hQ]
    simp only [ThomEncoding.sign, Polynomial.iterate_derivative_map, Polynomial.eval_map]
  have HR (k : ℕ) := IntegerPolynomialIndexedSampleTest.packet S (IntegerPolynomialIteratedDerivativeBits.source S)
    (f c) v (BinaryNatCode.encode k) hv
  simp only [language, Set.mem_ofPred_eq, source, scalarVertex, pairFst_pair, pairSnd_pair,
    SquareSampleCompleteVertices.language, hw, hv, true_and, agrees, jointProbe, scalarProbe]
  simp_rw [HJ, HR, IntegerPolynomialIteratedDerivativeBits.packet, SquareSampleTestSign.encode_eq_iff]
  constructor
  · intro hs
    apply ThomEncoding.root_eq ((S.polynomial (f c)).map (Int.castRingHom ℝ))
      ((Polynomial.map_ne_zero_iff Int.cast_injective).mpr hn) (S.degree (f c))
      (Polynomial.natDegree_map_le.trans (S.degree_bound _))
    · rwa [Polynomial.eval_map]
    · rw [Polynomial.eval_map]
      exact (IntegerPolynomialSampleInput.roots_iff S (f c) hn _).mp
        (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input S) (f c) v hv).property
    · intro k hk
      simpa only [ThomEncoding.sign, Polynomial.iterate_derivative_map, Polynomial.eval_map] using hs k (by omega)
  · intro he k _
    simp only [ThomEncoding.sign, Polynomial.iterate_derivative_map, Polynomial.eval_map, he]

end LeanCanny.Encoding.SquareSampleScalarCoordinateEquality
