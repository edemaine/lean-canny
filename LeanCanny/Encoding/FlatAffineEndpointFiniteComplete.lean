/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteSample
public import LeanCanny.Geometry.FlatAffineEndpointFiniteLift

/-! # Every actual midpoint tuple has a complete native label

Endpoint and derivative roots validate the charged degree preparation.
For a valid frame, any original current point and pair of endpoint roots
lift to a root with a short label accepted by the guarded native sampler.
Repeated heights and singular spatial roots remain included.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteSample
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

theorem record_valid (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (a t : ℝ) (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0)
    (ht : SymbolicScaledSquarefree.scalarEvaluation t (FlatAffineEndpointFiniteFrame.retained F height r) = 0) :
    FlatAffineEndpointFiniteFrame.Valid F height (FlatAffineEndpointFiniteFrame.record F height r) := by
  have hd : 0 < (FlatAffineEndpointFiniteFrame.retained F height r).natDegree :=
    Polynomial.natDegree_pos_of_eval₂_root (FlatAffineEndpointSamples.derivative_ne_zero F hcone height r hr a ha)
      (Int.castRingHom ℝ) ht (by intro z hz; change (z : ℝ) = 0 at hz; exact Int.cast_eq_zero.mp hz)
  simp only [FlatAffineEndpointFiniteFrame.Valid, FlatAffineEndpointFiniteFrame.record, FlatAffineEndpointFiniteFrame.degree,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact ⟨hr, FlatAffineEndpointValidity.degree_pos F hcone height r hr a ha, True.intro, hd⟩

theorem tuple_label_exists (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (a t : ℝ) (current left right : Fin (count F (pairFst (pairFst s))) → ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst s))) = 0)
    (ht : SymbolicScaledSquarefree.scalarEvaluation t (FlatAffineEndpointFiniteFrame.retained F height (pairFst s)) = 0)
    (hc : ∀ i, (FlatAffinePowerPositive.system F (pairFst (pairFst s)) i).eval₂ (Int.castRingHom ℝ) current =
      if i = height (pairFst (pairFst s)) then t else 0)
    (hl : ∀ i, (FlatAffinePowerPositive.system F (pairFst (pairFst s)) i).eval₂ (Int.castRingHom ℝ) left =
      if i = height (pairFst (pairFst s)) then a else 0)
    (hr : ∀ i, (FlatAffinePowerPositive.system F (pairFst (pairFst s)) i).eval₂ (Int.castRingHom ℝ) right =
      if i = height (pairFst (pairFst s)) then a else 0) :
    ∃ w, ∃ hw : SquareSampleCompleteVertices.Valid (input F hcone height) s w,
      pair s w ∈ GuardedSquareSampleInput.language (data F hcone height) ∧
        (SquareSampleCompleteVertices.candidate (input F hcone height) s w hw).val =
          Geometry.FlatAffineEndpointFiniteLift.point F s a t current left right := by
  let z := Geometry.FlatAffineEndpointFiniteLift.point F s a t current left right
  have hz := Geometry.FlatAffineEndpointFiniteLift.lift F height s a t current left right ha ht hc hl hr
  let root : SquareSampleComplete.Roots (input F hcone height) s :=
    ⟨z, (GuardedSquareSampleInput.roots_iff (data F hcone height) s hs z).mpr hz⟩
  let w := SquareSampleCompleteVertices.word (input F hcone height) (complete F hcone height) s root
  have hw := SquareSampleCompleteVertices.word_valid (input F hcone height) (complete F hcone height) s root
  refine ⟨w, hw, ?_, ?_⟩
  · change pairFst (pair s w) ∈ (data F hcone height).good ∧
      SquareSampleCompleteVertices.Valid (GuardedSquareSampleInput.input (data F hcone height))
        (pairFst (pair s w)) (pairSnd (pair s w))
    rw [pairFst_pair, pairSnd_pair]
    constructor
    · change FlatAffineEndpointFiniteFrame.Valid F height s
      exact hs
    · change SquareSampleCompleteVertices.Valid (input F hcone height) s w
      exact hw
  · exact congrArg (fun x : SquareSampleComplete.Roots (input F hcone height) s => x.val)
      (SquareSampleCompleteVertices.candidate_word (input F hcone height) (complete F hcone height) s root)

end LeanCanny.Encoding.FlatAffineEndpointFiniteSample
