/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegerPolynomialSampleSliceDegree

/-! # Complete scalar labels retain their values under query records -/

@[expose] public section
namespace LeanCanny.Encoding.IntegerPolynomialSampleSlice
open LeanCanny.Algebra LeanCanny.Computation
open IntegerPolynomialRootQueriesBits (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

theorem valid_packet (S : Source) (c w d : List Bool) : pair (pair c w) d ∈ valid S ↔
    SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input S) c w := by
  simp only [valid, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair]

theorem point_packet (S : Source) (c w d : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input S) c w) :
    point S (pair (pair c w) d) =
      (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input S) c w hw).val (0 : Fin 1) := by
  let valueAt (c w : List Bool) : ℝ := if hp : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input S) c w then
    (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input S) c w hp).val (0 : Fin 1) else 0
  change valueAt (pairFst (pairFst (pair (pair c w) d))) (pairSnd (pairFst (pair (pair c w) d))) = _
  rw [pairFst_pair, pairFst_pair, pairSnd_pair]
  exact dite_eq_left hw

end LeanCanny.Encoding.IntegerPolynomialSampleSlice
