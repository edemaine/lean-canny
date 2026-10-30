/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteComplete
public import LeanCanny.Algebra.FrozenRetainedMidpointSpace

/-! # Native midpoint signs at complete joint-frame labels

The linear integer midpoint test is read from original variable indices.
Native complete-root sign queries retain singular tuples. The guarded sign
language checks the degree record and the full original joint equations.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteMidpoint
open LeanCanny.Algebra LeanCanny.Computation MatrixPower Polynomial
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def test (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (index : (s : List Bool) → Fin (count F (pairFst (pairFst s)))) :
    SquareSamplePolynomialTest.Test (FlatAffineEndpointFiniteSample.input F hcone height) where
  polynomial s := Geometry.FlatAffineEndpointFiniteLift.midpoint F s (index s)
  degree _ := 1
  mass _ := 2
  polynomial_degree s := FrozenRetainedMidpointBits.degree_le (index s)
  polynomial_mass s := FrozenRetainedMidpointBits.mass_le (index s)

theorem testAccess {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (index : (s : List Bool) → Fin (count F (pairFst (pairFst s)))) (hi : UnaryFn (fun s => (index s).val)) :
    (test F hcone height index).Access := by
  have hc := RationalSubstitution.IntegerBits.context_mem_FP
  have hb := mem_FP_comp (mem_FP_comp hc pairFst_mem_FP) pairFst_mem_FP
  have E := FrozenRetainedMidpointBits.evaluator ((FlatAffineFullSourcePositive.count_unary h).comp hb) (UnaryFn.const (1 : ℕ).size)
    (fun q => index (RationalSubstitution.IntegerBits.context q)) (hi.comp hc)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP
  refine ⟨BinaryFn.const 1, BinaryFn.const 2, E.congr (funext fun q => ?_)⟩
  dsimp only [FixedWidthRowBits.value]
  rw [FixedWidthPolynomial.nativeExponent_refl]
  unfold SquareSamplePolynomialTest.coefficient SquareSamplePolynomialTest.family
    FixedWidthRationalSubstitutionBits.Family.coefficient SquareSamplePolynomialTest.width test
    Geometry.FlatAffineEndpointFiniteLift.midpoint FrozenRetainedMidpointBits.polynomial
  rfl

theorem evaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val))
    (index : (s : List Bool) → Fin (count F (pairFst (pairFst s)))) (hi : UnaryFn (fun s => (index s).val)) :
    SpaceFunction (SquareSampleCompletePolynomialTest.value (FlatAffineEndpointFiniteSample.input F hcone height)
      (test F hcone height index)) :=
  SquareSampleCompletePolynomialTest.evaluator (FlatAffineEndpointFiniteSample.sampleAccess h hcone height hh)
    (testAccess h hcone height index hi)

noncomputable def language (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (index : (s : List Bool) → Fin (count F (pairFst (pairFst s)))) (sigma : SignType) : Language :=
  {q | FlatAffineEndpointFiniteFrame.Valid F height (pairFst q) ∧ q ∈ SquareSampleCompletePolynomialTest.language
    (FlatAffineEndpointFiniteSample.input F hcone height) (test F hcone height index) sigma}

theorem decider {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val))
    (index : (s : List Bool) → Fin (count F (pairFst (pairFst s)))) (hi : UnaryFn (fun s => (index s).val)) (sigma : SignType) :
    SpaceDecider (language F hcone height index sigma) := by
  have V := ((FlatAffineEndpointFiniteFrame.validDecider h hcone height hh).precompose pairFst pairFst_mem_FP).flagEvaluator
  have E := (SquareSampleCompletePolynomialTest.decider (FlatAffineEndpointFiniteSample.sampleAccess h hcone height hh)
    (testAccess h hcone height index hi) sigma).flagEvaluator
  apply (V.andFlags E).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val))
    (index : (s : List Bool) → Fin (count F (pairFst (pairFst s)))) (hi : UnaryFn (fun s => (index s).val)) (sigma : SignType) :
    language F hcone height index sigma ∈ PSPACE := (decider h hcone height hh index hi sigma).mem_PSPACE

theorem tuple_sign (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (index : (s : List Bool) → Fin (count F (pairFst (pairFst s)))) (sigma : SignType) (s w : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F hcone height) s w)
    (a t : ℝ) (current left right : Fin (count F (pairFst (pairFst s))) → ℝ)
    (he : (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F hcone height) s w hw).val =
      Geometry.FlatAffineEndpointFiniteLift.point F s a t current left right) :
    pair s w ∈ language F hcone height index sigma ↔
      SignType.sign (2 * current (index s) - left (index s) - right (index s)) = sigma := by
  simp only [language, Set.mem_ofPred_eq, pairFst_pair, hs, true_and]
  rw [SquareSampleCompletePolynomialTest.language_packet _ _ _ _ _ hw]
  have H := congrArg (fun z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ =>
    (Geometry.FlatAffineEndpointFiniteLift.midpoint F s (index s)).eval₂ (Int.castRingHom ℝ) z) he
  have hm := H.trans (Geometry.FlatAffineEndpointFiniteLift.midpoint_eval F s (index s) a t current left right)
  exact Iff.of_eq (congrArg (fun z : ℝ => SignType.sign z = sigma) hm)

end LeanCanny.Encoding.FlatAffineEndpointFiniteMidpoint
