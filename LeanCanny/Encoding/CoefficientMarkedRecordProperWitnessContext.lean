/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessLayout
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalFullSemantics
/-! # Each coordinate witness word is its own actual prepared full sample -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessContext
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedRoadmapProperRow CoefficientMarkedRecordProperWitnessLayout
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem candidate_factor (I J : SquareSampleInput.Inputs) (f : List Bool → List Bool)
    (h : I = SquareSampleInput.comp J f) (q w : List Bool)
    (hi : SquareSampleCompleteVertices.Valid I q w)
    (hj : SquareSampleCompleteVertices.Valid J (f q) w) :
    HEq (SquareSampleCompleteVertices.candidate I q w hi).val
      (SquareSampleCompleteVertices.candidate J (f q) w hj).val := by
  cases h
  exact heq_of_eq (SquareSampleCompleteNaturality.candidate_comp J f q w hi hj)

private theorem candidate_context (I : SquareSampleInput.Inputs) (c d w : List Bool) (h : c = d)
    (hc : SquareSampleCompleteVertices.Valid I c w) (hd : SquareSampleCompleteVertices.Valid I d w) :
    HEq (SquareSampleCompleteVertices.candidate I c w hc).val
      (SquareSampleCompleteVertices.candidate I d w hd).val := by
  cases h
  rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "S" => IntegralMixedPhysicalMarkedTest.input hn ht ha (IntegralMixedOriginalRegularSource.radius_binary hR) false

theorem valid_prepared (mean : Bool) (z baseWord own : List Bool) :
    SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR mean) (request z baseWord) own ↔
      SquareSampleCompleteVertices.Valid S (preparedContext n mean z) own := by
  rw [valid_at_context hn ht ha hR mean, native_context hn ht ha hR]

/-- Complete input composition includes numerical sampling metadata; this
identifies the entire SAME-radius own tuple, not just its defining system. -/
theorem candidate_prepared (mean : Bool) (z baseWord own : List Bool)
    (hi : SquareSampleCompleteVertices.Valid (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR mean) (request z baseWord) own)
    (hs : SquareSampleCompleteVertices.Valid S (preparedContext n mean z) own) :
    HEq (SquareSampleCompleteVertices.candidate (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR mean)
      (request z baseWord) own hi).val
      (SquareSampleCompleteVertices.candidate S (preparedContext n mean z) own hs).val := by
  let hctx := (valid_at_context hn ht ha hR mean (request z baseWord) own).mp hi
  have HC := candidate_factor _ S (context hn ht ha hR mean) (sampler_comp hn ht ha hR mean)
    (request z baseWord) own hi hctx
  exact HC.trans (candidate_context S _ _ own (native_context hn ht ha hR mean z baseWord) hctx hs)

theorem width_prepared (mean : Bool) (z baseWord : List Bool) :
    SquareSampleCompleteVertices.width (CoefficientMarkedRecordProperWordTuple.input hn ht ha hR mean) (request z baseWord) =
      SquareSampleCompleteVertices.width S (preparedContext n mean z) := by
  change SquareSampleCompleteVertices.width
    (IntegralFramedPhysicalSquare.input _ _ _ _ _ _ _ (terminal hn ht ha hR mean) (positive hn ht ha hR mean)) _ = _
  rw [sampler_comp hn ht ha hR mean, SquareSampleCompleteNaturality.complete_width_comp, native_context hn ht ha hR]

end LeanCanny.Encoding.CoefficientMarkedRecordProperWitnessContext
