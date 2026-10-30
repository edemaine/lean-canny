/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteParameterChoice
public import LeanCanny.Encoding.IntegerPolynomialSampleSliceRootCount

/-! # Native algebraic slice readers over an original complete point label

Input `((source, parent point), child fields)` retains the original parent
record. The scalar primitive-parameter record is computed internally. Native
coefficient signs, actual degrees, and distinct-root counts of the child
bivariate family therefore require no supplied algebraic coefficient oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteParameterSlice
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open SquareSampleCompleteParameterTest (source theta)
open BoundedAlgebraicSlice (Family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def query (F : Inputs) (u : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst u)) (SquareSampleCompleteParameterChoice.value F (pairFst u))) (pairSnd u)

theorem queryEvaluator {F : Inputs} (h : F.Access) : SpaceFunction (query F) := by
  have E := ((SquareSampleCompleteParameterChoice.evaluator h).precompose pairFst pairFst_mem_FP).withInput
  exact (E.postcompose (fun r => pair (pair (pairFst (pairFst (pairFst r))) (pairSnd r)) (pairSnd (pairFst r)))
    (by polytime)).congr (funext fun u => by simp only [query, Function.comp_apply, pairFst_pair, pairSnd_pair])

theorem query_valid (F : Inputs) (c w d : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    query F (pair (pair c w) d) ∈ IntegerPolynomialSampleSlice.valid (source F) := by
  simpa only [query, pairFst_pair, pairSnd_pair] using
    (IntegerPolynomialSampleSlice.valid_packet (source F) c (SquareSampleCompleteParameterChoice.value F (pair c w)) d).mpr
      (SquareSampleCompleteParameterChoice.scalar_valid F c w hw)

theorem query_point (F : Inputs) (c w d : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    IntegerPolynomialSampleSlice.point (source F) (query F (pair (pair c w) d)) = theta F c w := by
  have H := IntegerPolynomialSampleSlice.point_packet (source F) c (SquareSampleCompleteParameterChoice.value F (pair c w)) d
    (SquareSampleCompleteParameterChoice.scalar_valid F c w hw)
  simpa only [query, pairFst_pair, pairSnd_pair] using H.trans (SquareSampleCompleteParameterChoice.value_packet F c w hw)

theorem specialized_packet (F : Inputs) (Q : Family) (c w d : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    IntegerPolynomialSampleSlice.specialized (source F) Q (query F (pair (pair c w) d)) = Q.slice (pair c d) (theta F c w) := by
  rw [IntegerPolynomialSampleSlice.specialized, ite_eq_left (query_valid F c w d hw), query_point F c w d hw]
  simp only [IntegerPolynomialSampleSlice.context, query, pairFst_pair, pairSnd_pair]

noncomputable def coefficientQuery (F : Inputs) (r : List Bool) : List Bool := pair (query F (pairFst r)) (pairSnd r)
theorem coefficientQueryEvaluator {F : Inputs} (h : F.Access) : SpaceFunction (coefficientQuery F) :=
  ((queryEvaluator h).precompose pairFst pairFst_mem_FP).pairOutputs (SpaceFunction.ofFP pairSnd pairSnd_mem_FP)

noncomputable def coefficientSign (F : Inputs) (Q : Family) : List Bool → List Bool :=
  IntegerPolynomialSampleSlice.coefficientSign (source F) Q ∘ coefficientQuery F

theorem coefficientSignEvaluator {F : Inputs} (h : F.Access) {Q : Family} (A : Q.Access) :
    SpaceFunction (coefficientSign F Q) :=
  (coefficientQueryEvaluator h).chain
    (IntegerPolynomialSampleSlice.coefficientSignEvaluator (SquareSampleCompleteParameterTest.sourceAccess h) A)

theorem coefficientSign_packet (F : Inputs) (Q : Family) (c w d : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F c w) (k : ℕ) :
    coefficientSign F Q (pair (pair (pair c w) d) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign ((Q.slice (pair c d) (theta F c w)).coeff k)) := by
  unfold coefficientSign
  simp only [Function.comp_apply, coefficientQuery, pairFst_pair, pairSnd_pair]
  rw [IntegerPolynomialSampleSlice.coefficientSign_packet, specialized_packet F Q c w d hw]

theorem degreeEvaluator {F : Inputs} (h : F.Access) {Q : Family} (A : Q.Access) :
    SpaceFunction (fun u => BinaryNatCode.encode
      (IntegerPolynomialSampleSlice.specialized (source F) Q (query F u)).natDegree) :=
  (queryEvaluator h).chain (IntegerPolynomialSampleSlice.degreeEvaluator (SquareSampleCompleteParameterTest.sourceAccess h) A)

theorem rootCountEvaluator {F : Inputs} (h : F.Access) {Q : Family} (A : Q.Access) :
    SpaceFunction (fun u => BinaryNatCode.encode (IntegerPolynomialSampleSlice.RootCount.count (source F) Q (query F u))) :=
  (queryEvaluator h).chain (IntegerPolynomialSampleSlice.RootCount.count_evaluator (SquareSampleCompleteParameterTest.sourceAccess h) A)

end LeanCanny.Encoding.SquareSampleCompleteParameterSlice
