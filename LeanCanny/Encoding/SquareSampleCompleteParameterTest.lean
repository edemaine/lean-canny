/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteIndexedPolynomialTest
public import LeanCanny.Encoding.IntegerPolynomialIndexedSampleTest

/-! # Native scalar tests at the primitive parameter of a complete point

The original complete point label also specifies a primitive parameter root.
Indexed univariate tests access that root directly, preserving the point's
original source, selected grid, hash, and ordinal. This permits scalar slice
records to share the exact algebraic data of a parent point, including a
singular point of the original system.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteParameterTest
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open IntegerPolynomialRootQueriesBits (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def source (F : Inputs) : Source where
  polynomial := SquareSampleCoordinates.parameter F
  degree := SquareSampleCoordinates.parameterDegree F
  mass := SquareSampleCoordinates.baseHeight F
  degree_bound c := (SquareSampleCoordinates.parameter_bounds F c).1
  mass_bound c := (SquareSampleCoordinates.parameter_bounds F c).2

theorem sourceAccess {F : Inputs} (h : F.Access) : IntegerPolynomialRootQueriesBits.Access (source F) :=
  ⟨SquareSampleCoordinates.parameter_coefficient_evaluator h,
    SquareSampleCoordinates.parameterDegree_binary h, SquareSampleCoordinates.baseHeight_binary h⟩

noncomputable def theta (F : Inputs) (c w : List Bool) : ℝ :=
  if hw : SquareSampleCompleteVertices.Valid F c w then
    (SquareSampleCompleteVertices.theta F c w (Classical.choose hw)).val else 0

theorem theta_packet (F : Inputs) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    theta F c w = (SquareSampleCompleteVertices.theta F c w (Classical.choose hw)).val := dite_eq_left hw

theorem theta_root (F : Inputs) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    ((source F).polynomial c).eval₂ (Int.castRingHom ℝ) (theta F c w) = 0 := by
  have H := (SquareSampleQueries.mem_roots (SquareSampleGrid.input F) c
    (SquareSampleCompleteVertices.theta F c w (Classical.choose hw)).val).mp
    (SquareSampleCompleteVertices.theta F c w (Classical.choose hw)).property
  rw [SquareSampleGrid.parameter_eq] at H
  rw [theta_packet F c w hw]
  exact H.1

theorem decode_theta (F : Inputs) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    SquareSampleParameters.decode F c (theta F c w) = (SquareSampleCompleteVertices.candidate F c w hw).val := by
  rw [theta_packet F c w hw]
  exact (SquareSampleCompleteVertices.point_decode F c w (Classical.choose hw)).symm

def normalize (z : List Bool) : List Bool := pair (pairFst z) (pairSnd z)
theorem normalize_FP : normalize ∈ FP := by polytime [normalize]

noncomputable def test (Q : Source) : SquareSampleTestMoments.Test where
  polynomial z := Q.polynomial (normalize z)
  degree z := Q.degree (normalize z)
  mass z := Q.mass (normalize z)
  polynomial_degree z := Q.degree_bound (normalize z)
  polynomial_mass z := Q.mass_bound (normalize z)

noncomputable def testAccess {Q : Source} (A : IntegerPolynomialRootQueriesBits.Access Q) : (test Q).Access :=
  SquareSampleTestMoments.Test.Access.ofPrimitive (A.degree.comp normalize_FP) (A.mass.comp normalize_FP)
    (PolynomialFamilyProductBits.reindexEvaluator A.coefficient normalize normalize_FP)

noncomputable def value (F : Inputs) (Q : Source) : List Bool → List Bool :=
  SquareSampleIndexedSign.atOrdinal (SquareSampleGrid.input F) (test Q) ∘ SquareSampleCompleteIndexedPolynomialTest.query

theorem evaluator {F : Inputs} (h : F.Access) {Q : Source} (A : IntegerPolynomialRootQueriesBits.Access Q) :
    SpaceFunction (value F Q) :=
  (SquareSampleIndexedSign.ordinal_evaluator (SquareSampleGrid.access h) (testAccess A)).precompose
    SquareSampleCompleteIndexedPolynomialTest.query SquareSampleCompleteIndexedPolynomialTest.query_FP

theorem packet (F : Inputs) (Q : Source) (c w d : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    value F Q (pair (pair c w) d) = InfinitesimalSign.encode (SignType.sign
      ((Q.polynomial (pair c d)).eval₂ (Int.castRingHom ℝ) (theta F c w))) := by
  have H := SquareSampleIndexedSign.ordinal_packet (SquareSampleGrid.input F) (test Q) c d
    ⟨Nat.fromBitsLE w, (Classical.choose hw).2⟩
  simpa only [value, Function.comp_apply, SquareSampleCompleteIndexedPolynomialTest.query, pairFst_pair, pairSnd_pair,
    BinaryNat.normalize_eq_bits, BinaryNatCode.encode, SquareSampleTestMoments.sign, test, normalize,
    Polynomial.eval_map, theta_packet F c w hw, SquareSampleCompleteVertices.theta] using H

end LeanCanny.Encoding.SquareSampleCompleteParameterTest
