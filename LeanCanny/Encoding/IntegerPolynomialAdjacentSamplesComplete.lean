/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegerPolynomialAdjacentSamples
public import LeanCanny.Encoding.IntegerPolynomialSampleSlicePoint

/-! # Complete labels for algebraic samples in adjacent gaps -/

@[expose] public section
namespace LeanCanny.Encoding.IntegerPolynomialAdjacentSamples
open LeanCanny.Algebra LeanCanny.Computation
open IntegerPolynomialRootQueriesBits (Source)
open Geometry.OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

theorem sample_label_complete_point (S T Q : Source) (right : Bool) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input S) c w)
    (i : Fin (IntegerPolynomialRootQueriesBits.rootSet Q c).card)
    (hi : root (IntegerPolynomialRootQueriesBits.rootSet Q c) i =
      (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input S) c w hw).val (0 : Fin 1))
    (t : ℝ) (hT : T.polynomial c ≠ 0) (ht : (T.polynomial c).eval₂ (Int.castRingHom ℝ) t = 0)
    (hgap : t ∈ gap (IntegerPolynomialRootQueriesBits.rootSet Q c) (if right then rightGap _ i else leftGap _ i)) :
    ∃ v, ∃ hv : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input T) c v,
      (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input T) c v hv).val (0 : Fin 1) = t ∧
        pair (pair c w) v ∈ language S T Q right := by
  obtain ⟨v, hv, he⟩ := IntegerPolynomialSampleInput.root_complete T c hT t ht
  let q := pair (pair c w) v
  have ha : endpointRecord q ∈ IntegerPolynomialSampleSlice.valid S := by
    simpa only [q, endpointRecord, pairFst_pair, pairSnd_pair, IntegerPolynomialSampleSlice.valid,
      Set.mem_ofPred_eq] using hw
  have hb : sampleRecord q ∈ IntegerPolynomialSampleSlice.valid T := by
    simpa only [q, sampleRecord, pairFst_pair, pairSnd_pair, IntegerPolynomialSampleSlice.valid,
      Set.mem_ofPred_eq] using hv
  have hpa : IntegerPolynomialSampleSlice.point S (endpointRecord q) =
      (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input S) c w hw).val (0 : Fin 1) := by
    simpa only [q, endpointRecord, pairFst_pair, pairSnd_pair] using IntegerPolynomialSampleSlice.point_packet S c w [] hw
  have hpb : IntegerPolynomialSampleSlice.point T (sampleRecord q) = t := by
    simpa only [q, sampleRecord, pairFst_pair, pairSnd_pair] using (IntegerPolynomialSampleSlice.point_packet T c v [] hv).trans he
  have H : t ∉ IntegerPolynomialRootQueriesBits.rootSet Q c ∧
      lowerCount (IntegerPolynomialRootQueriesBits.rootSet Q c) t =
        lowerCount (IntegerPolynomialRootQueriesBits.rootSet Q c) (root (IntegerPolynomialRootQueriesBits.rootSet Q c) i) +
          if right then 1 else 0 := by
    cases right
    · simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using (mem_leftGap_iff_rank _ i t).mp hgap
    · simpa only [ite_true] using (mem_rightGap_iff_rank _ i t).mp hgap
  refine ⟨v, hv, he, (language_iff S T Q right q ha hb).mpr ?_⟩
  simpa only [q, pairFst_pair, hpa, hpb, ← hi] using
    (show root (IntegerPolynomialRootQueriesBits.rootSet Q c) i ∈ IntegerPolynomialRootQueriesBits.rootSet Q c ∧
      t ∉ IntegerPolynomialRootQueriesBits.rootSet Q c ∧
      lowerCount (IntegerPolynomialRootQueriesBits.rootSet Q c) t =
        lowerCount (IntegerPolynomialRootQueriesBits.rootSet Q c) (root (IntegerPolynomialRootQueriesBits.rootSet Q c) i) +
          if right then 1 else 0 from ⟨root_mem _ i, H⟩)

theorem sample_label_complete (S T Q : Source) (right : Bool) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input S) c w)
    (i : Fin (IntegerPolynomialRootQueriesBits.rootSet Q c).card)
    (hi : root (IntegerPolynomialRootQueriesBits.rootSet Q c) i =
      (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input S) c w hw).val (0 : Fin 1))
    (t : ℝ) (hT : T.polynomial c ≠ 0) (ht : (T.polynomial c).eval₂ (Int.castRingHom ℝ) t = 0)
    (hgap : t ∈ gap (IntegerPolynomialRootQueriesBits.rootSet Q c) (if right then rightGap _ i else leftGap _ i)) :
    ∃ v, pair (pair c w) v ∈ language S T Q right := by
  obtain ⟨v, _, _, hv⟩ := sample_label_complete_point S T Q right c w hw i hi t hT ht hgap
  exact ⟨v, hv⟩

end LeanCanny.Encoding.IntegerPolynomialAdjacentSamples
