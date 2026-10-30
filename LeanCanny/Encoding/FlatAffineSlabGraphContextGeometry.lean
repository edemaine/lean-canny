/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSlabGraphContext
public import LeanCanny.Geometry.OrderedRealCellRefinement

/-! # Geometric values and gaps supplied by native slab-context validation -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSlabGraphContext
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes (source gapWord endpointWord sampleWord)
open OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def roots (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool) : Finset ℝ :=
  FlatAffineEndpointSampleSlab.roots F cone height (source c)
noncomputable def refinedRoots (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool) : Finset ℝ :=
  FlatAffineEndpointCells.roots F cone height (pairFst (source c))

theorem sample_location (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) (hc : c ∈ language F cone height) :
    sampleValue F cone height side c ∉ roots F cone height c ∧
      lowerCount (roots F cone height c) (sampleValue F cone height side c) = Nat.fromBitsLE (gapWord c) := by
  let S := FlatAffineEndpointSamples.source F cone height
  let Q := FlatAffineEndpointAdjacentSamples.heightSource F cone height
  have HV := sample_record_valid F cone height side c hc
  have CTX : pairFst (pairFst (sampleRecord side c)) = pairFst (source c) := by
    rw [sampleRecord_packet, pairFst_pair, pairFst_pair]
  have HC := IntegerPolynomialAlgebraicCut.count_below S Q (sampleRecord side c) HV
  have HZ := IntegerPolynomialAlgebraicCut.zeroCount_eq_zero_iff S Q (sampleRecord side c) HV
  rw [CTX] at HC HZ
  change IntegerPolynomialAlgebraicCut.count S Q (sampleRecord side c) =
    lowerCount (roots F cone height c) (sampleValue F cone height side c) at HC
  change IntegerPolynomialAlgebraicCut.zeroCount S Q (sampleRecord side c) = 0 ↔
    sampleValue F cone height side c ∉ roots F cone height c at HZ
  have N : FlatAffineEndpointSampleSlab.numeric F cone height (numericQuery side c) := by
    cases side
    · exact hc.2.2.2.1
    · exact hc.2.2.2.2
  have EQ : FlatAffineEndpointSampleSlab.record (numericQuery side c) = sampleRecord side c := by
    rw [sampleRecord_packet]
    simp only [FlatAffineEndpointSampleSlab.record, FlatAffineEndpointSampleSlab.sampleWord,
      numericQuery, pairFst_pair, pairSnd_pair]
  unfold FlatAffineEndpointSampleSlab.numeric at N
  rw [EQ] at N
  simp only [FlatAffineEndpointSampleSlab.gapWord, numericQuery, pairSnd_pair] at N
  exact ⟨HZ.mp N.2, HC.symm.trans N.1⟩

noncomputable def gapIndex (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool) (hc : c ∈ language F cone height) :
    Fin ((roots F cone height c).card + 1) :=
  ⟨Nat.fromBitsLE (gapWord c), by
    have H := (sample_location F cone height false c hc).2
    have HB : lowerCount (roots F cone height c) (sampleValue F cone height false c) ≤ (roots F cone height c).card :=
      Finset.card_filter_le _ _
    omega⟩

theorem sample_in_gap (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) (hc : c ∈ language F cone height) :
    sampleValue F cone height side c ∈ gap (roots F cone height c) (gapIndex F cone height c hc) :=
  (mem_gap_iff_rank _ _ _).mpr (sample_location F cone height side c hc)

theorem endpoint_root (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) (hc : c ∈ language F cone height) :
    SymbolicScaledSquarefree.scalarEvaluation (endpointValue F cone height side c)
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst (source c)))) = 0 := by
  have HR := (IntegerPolynomialSampleInput.roots_iff (FlatAffineEndpointAdjacentSamples.heightSource F cone height) (pairFst (source c))
    (FlatAffineHeightSlabExceptional.ne_zero F cone height (pairFst (pairFst (source c)))) _).mp
    (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst (source c)) (endpointWord side c)
      (endpoint_label_valid F cone height side c hc)).property
  exact (congrArg (fun a : ℝ => SymbolicScaledSquarefree.scalarEvaluation a
    (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst (source c)))) = 0)
      (endpointValue_packet F cone height side c hc)).mpr HR

theorem endpoint_mem (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) (hc : c ∈ language F cone height) :
    endpointValue F cone height side c ∈ roots F cone height c :=
  (FlatAffineHeightCells.mem_roots_iff F cone height (pairFst (pairFst (source c))) _).mpr (endpoint_root F cone height side c hc)

theorem original_subset_refined (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool) (hc : c ∈ language F cone height) :
    roots F cone height c ⊆ refinedRoots F cone height c := by
  intro a ha
  have HR : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst (source c)))) = 0 :=
    (FlatAffineHeightCells.mem_roots_iff F cone height (pairFst (pairFst (source c))) a).mp ha
  exact FlatAffineEndpointCells.endpoint_mem F cone height (pairFst (source c)) hc.1.1 a HR

theorem adjacent_ranks (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) (hc : c ∈ language F cone height) :
    endpointValue F cone height side c ∈ refinedRoots F cone height c ∧
      sampleValue F cone height side c ∉ refinedRoots F cone height c ∧
      lowerCount (refinedRoots F cone height c) (sampleValue F cone height side c) =
        lowerCount (refinedRoots F cone height c) (endpointValue F cone height side c) + if !side then 1 else 0 := by
  have H := adjacent_valid F cone height side c hc
  unfold FlatAffineEndpointAdjacentSamples.language at H
  have HP := (IntegerPolynomialAdjacentSamples.language_iff (FlatAffineEndpointAdjacentSamples.heightSource F cone height)
    (FlatAffineEndpointSamples.source F cone height) (FlatAffineEndpointCells.source F cone height) (!side) (adjacentQuery side c)
    (endpoint_record_valid F cone height side c hc) (sample_record_valid F cone height side c hc)).mp H.2
  have CTX : pairFst (pairFst (adjacentQuery side c)) = pairFst (source c) := by simp only [adjacentQuery, pairFst_pair]
  rw [CTX] at HP
  exact HP

theorem refined_gap (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) (hc : c ∈ language F cone height)
    (i : Fin (refinedRoots F cone height c).card)
    (hi : root (refinedRoots F cone height c) i = endpointValue F cone height side c) :
    sampleValue F cone height side c ∈ gap (refinedRoots F cone height c)
      (if !side then rightGap _ i else leftGap _ i) := by
  have H := adjacent_ranks F cone height side c hc
  rw [← hi] at H
  cases side
  · exact (mem_rightGap_iff_rank _ i _).mpr H.2
  · apply (mem_leftGap_iff_rank _ i _).mpr
    simpa only [Bool.not_true, Bool.false_eq_true, ite_false, Nat.add_zero] using H.2

end LeanCanny.Encoding.FlatAffineSlabGraphContext
