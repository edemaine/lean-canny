/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalEndpointFrame

/-! # Original-source size bounds for exceptional parameter frames

Exact degree records are computed natively. For those canonical source
records, every valid endpoint marker and its computed parent fit one
polynomial in the original source length. Arbitrarily padded degree records
are not silently charged to the shorter original source.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalEndpointFrame
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (row parentCone)
open scoped Classical

noncomputable def canonicalSource (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) : List Bool :=
  FlatAffineEndpointFiniteFrame.record (next F) (row F h)
    (FlatAffineEndpointPreparation.record (next F) (row F h) u)

theorem canonicalSource_evaluator {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    SpaceFunction (canonicalSource F h) :=
  (FlatAffineEndpointPreparation.recordEvaluator
    (FlatAffineCompleteRootStages.access hF (hF.depth.add (UnaryFn.const 1))) C (row F h)
    (FlatAffineLastHeightRow.row_unary hF h hh)).chain
      (FlatAffineEndpointFiniteFrame.recordEvaluator
        (FlatAffineCompleteRootStages.access hF (hF.depth.add (UnaryFn.const 1))) C (row F h)
        (FlatAffineLastHeightRow.row_unary hF h hh))

theorem canonicalSource_original (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) :
    FlatAffineJointPrefixChoice.original (canonicalSource F h u) = u := by
  simp only [FlatAffineJointPrefixChoice.original, canonicalSource, FlatAffineEndpointFiniteFrame.record,
    FlatAffineEndpointPreparation.record, pairFst_pair]

noncomputable def envelope (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (s : List Bool) : List Bool :=
  pair (pair (pair s (List.replicate
      (SquareSampleCompleteVertices.width (IntegerPolynomialSampleInput.input
        (FlatAffineEndpointAdjacentSamples.heightSource (next F) C (row F h))) (pairFst s)) false))
    (List.replicate (SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input (next F) C (row F h)) s) false))
    (List.replicate (SquareSampleCompleteVertices.width (FlatAffinePowerSampleInput.input F (parentCone F C))
      (FlatAffineJointPrefixChoice.original s)) false)

theorem envelope_FP {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) : envelope F C h ∈ FP := by
  have hNext := FlatAffineCompleteRootStages.access hF (hF.depth.add (UnaryFn.const 1))
  have hRow := FlatAffineLastHeightRow.row_unary hF h hh
  have A := ((SquareSampleCompleteVertices.width_unary
    (IntegerPolynomialSampleInput.access (FlatAffineEndpointAdjacentSamples.heightAccess hNext C (row F h) hRow))).comp
    pairFst_mem_FP).replicate_mem_FP false
  have J := (FlatAffineEndpointFiniteSample.width_unary hNext C (row F h) hRow).replicate_mem_FP false
  have P := ((SquareSampleCompleteVertices.width_unary (FlatAffinePowerSampleInput.access hF (parentCone F C))).comp
    FlatAffineJointPrefixChoice.original_FP).replicate_mem_FP false
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair id_mem_FP A) J) P

theorem frame_length_eq_envelope (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (s a w : List Bool)
    (hq : pair (pair s a) w ∈ FlatAffineEndpointMarkers.language (next F) C (row F h)) :
    (frame F C h (pair (pair s a) w)).length = (envelope F C h s).length := by
  have A := (Classical.choose (FlatAffineEndpointMarkers.endpoint_valid (next F) C (row F h) _ hq)).1
  have J := FlatAffineEndpointMarkers.valid_length (next F) C (row F h) _ hq
  have P := FlatAffineCompleteVertices.word_length F (parentCone F C) _ _
    (FlatAffineEndpointCanonicalParent.value_valid F C h _ hq)
  simp only [FlatAffineEndpointMarkers.source, FlatAffineEndpointMarkers.endpointWord,
    FlatAffineEndpointMarkers.jointWord, pairFst_pair, pairSnd_pair] at A J P
  simp only [frame, envelope, pair_length, List.length_replicate, A, J, P]
  rfl

theorem canonical_frame_polynomial {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    ∃ p : Polynomial ℕ, ∀ u a w,
      pair (pair (canonicalSource F h u) a) w ∈ FlatAffineEndpointMarkers.language (next F) C (row F h) →
        (frame F C h (pair (pair (canonicalSource F h u) a) w)).length ≤ p.eval u.length := by
  obtain ⟨p, hp⟩ := ((canonicalSource_evaluator hF C h hh).postcompose _ (envelope_FP hF C h hh)).exists_output_length_poly
  refine ⟨p, ?_⟩
  intro u a w hq
  exact (frame_length_eq_envelope F C h _ a w hq).le.trans (hp u)

end LeanCanny.Encoding.FlatAffineExceptionalEndpointFrame
