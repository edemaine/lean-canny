/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointAdjacentSamples
public import LeanCanny.Encoding.IntegerPolynomialAdjacentSamplesComplete

/-! # Every bounded endpoint gap has a native accepted algebraic sample

Complete endpoint labels retain singular heights. Rolle samples in bounded
refined gaps have complete labels accepted by the native adjacency validator.
No endpoint or sample regularity is required.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointAdjacentSamples
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open Geometry.OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

theorem sample_exists (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (r w : List Bool)
    (hr : FlatAffineEndpointValidity.Valid F height r)
    (hw : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (heightSource F hcone height)) r w)
    (i : Fin (FlatAffineEndpointCells.roots F hcone height r).card)
    (hi : root (FlatAffineEndpointCells.roots F hcone height r) i =
      (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input (heightSource F hcone height)) r w hw).val (0 : Fin 1))
    (h0 : 0 < (if right then rightGap _ i else leftGap _ i).val)
    (hk : (if right then rightGap _ i else leftGap _ i).val < (FlatAffineEndpointCells.roots F hcone height r).card) :
    ∃ v, pair (pair r w) v ∈ language F hcone height right := by
  let a := (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input (heightSource F hcone height)) r w hw).val (0 : Fin 1)
  have ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0 :=
    (IntegerPolynomialSampleInput.roots_iff (heightSource F hcone height) r
      (FlatAffineHeightSlabExceptional.ne_zero F hcone height (pairFst r)) _).mp
        (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input (heightSource F hcone height)) r w hw).property
  obtain ⟨t, ht, hgap⟩ := FlatAffineEndpointSamples.exists_in_gap F hcone height r hr a ha _ h0 hk
  obtain ⟨v, hv⟩ := IntegerPolynomialAdjacentSamples.sample_label_complete (heightSource F hcone height)
    (FlatAffineEndpointSamples.source F hcone height) (FlatAffineEndpointCells.source F hcone height) right r w hw i hi t
    (FlatAffineEndpointSamples.derivative_ne_zero F hcone height r hr a ha)
    ((FlatAffineEndpointSamples.mem_roots_iff F hcone height r hr a ha t).mp ht) hgap
  refine ⟨v, ?_, hv⟩
  simpa only [pairFst_pair] using hr

end LeanCanny.Encoding.FlatAffineEndpointAdjacentSamples
