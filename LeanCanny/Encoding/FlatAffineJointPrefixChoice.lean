/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineShiftPrefixInput
public import LeanCanny.Encoding.FlatAffineEndpointFiniteSample
public import LeanCanny.Geometry.FlatAffineEndpointFiniteProjection
public import LeanCanny.Encoding.SquareSampleProjectionChoiceAt

/-! # Native frozen ancestor labels from actual joint branch samples

The complete joint label supplies its current spatial copy. The varied row
determines the frozen prefix sampler, and native projection search computes
its exact complete ancestor label. Correctness uses the validated frame and
the fact that an original row, rather than the extra zero row, is varied.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineJointPrefixChoice
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

def original (s : List Bool) : List Bool := pairFst (pairFst s)
theorem original_FP : original ∈ FP := by polytime [original]

noncomputable def target (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : SquareSampleInput.Inputs :=
  SquareSampleInput.comp (FlatAffineShiftPrefixInput.input F C height) original

theorem targetAccess {F : Inputs} (h : F.Access) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : (target F C height).Access :=
  SquareSampleInput.access_comp (FlatAffineShiftPrefixInput.inputAccess h C height hh) original_FP

theorem targetComplete (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : SquareSampleComplete.Complete (target F C height) :=
  fun s => FlatAffinePowerSampleInput.complete (FlatAffineShiftPrefixInput.inputs F height)
    (FlatAffineShiftPrefixInput.cone F C height) (original s)

noncomputable def projection (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool)
    (i : Fin ((target F C height).count s)) : Fin ((FlatAffineEndpointFiniteSample.input F C height).count s) :=
  FlatAffineEndpointFiniteProjection.slot F s 0
    (FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height)
      (FlatAffineShiftPrefixInput.depth_le F height) (original s) i)

noncomputable def indexAt (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u d : List Bool) : ℕ :=
  (SquareSampleProjectedThom.coordinate (FlatAffinePowerSampleInput.input F C)
    (FlatAffineShiftPrefixInput.input F C height)
    (FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height) (FlatAffineShiftPrefixInput.depth_le F height)) u d).val

theorem index_unary {F : Inputs} (h : F.Access) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    UnaryFn (fun q => indexAt F C height (pairFst q) (pairSnd q)) :=
  FlatAffinePowerPrefix.coordinate_unary h (FlatAffineShiftPrefixInput.depth_unary h height hh) (FlatAffineShiftPrefixInput.depth_le F height) C

lemma coordinate_val (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s d : List Bool) :
    (SquareSampleProjectedThom.coordinate (FlatAffineEndpointFiniteSample.input F C height) (target F C height)
      (projection F C height) s d).val =
    indexAt F C height (original s) d + 2 := by
  unfold indexAt SquareSampleProjectedThom.coordinate projection
  rw [FlatAffineEndpointFiniteProjection.slot_val]
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero]
  rfl

def prepare (q : List Bool) : List Bool := pair (original (pairFst q)) (pairSnd q)
theorem prepare_FP : prepare ∈ FP := mem_FP_pair (mem_FP_comp (f := pairFst) (g := original) pairFst_mem_FP original_FP) pairSnd_mem_FP

attribute [local irreducible] indexAt

theorem coordinate_unary {F : Inputs} (h : F.Access) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    UnaryFn (fun q => (SquareSampleProjectedThom.coordinate (FlatAffineEndpointFiniteSample.input F C height) (target F C height)
      (projection F C height) (pairFst q) (pairSnd q)).val) := by
  have A := (index_unary h C height hh).comp prepare_FP
  apply (A.add (UnaryFn.const 2)).of_eq
  intro q
  simp only [prepare, pairFst_pair, pairSnd_pair]
  exact (coordinate_val F C height (pairFst q) (pairSnd q)).symm

noncomputable def value (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : List Bool → List Bool :=
  SquareSampleProjectionChoice.value (FlatAffineEndpointFiniteSample.input F C height) (target F C height) (projection F C height)

theorem evaluator {F : Inputs} (h : F.Access) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (value F C height) :=
  SquareSampleProjectionChoice.evaluator (FlatAffineEndpointFiniteSample.sampleAccess h C height hh)
    (targetAccess h C height hh) (projection F C height) (coordinate_unary h C height hh)

theorem projects (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hold : (height (original s)).val < FlatAffineFullSourceTower.count F (original s))
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F C height) s w) :
    ∀ i, ((target F C height).system s i).eval₂ (Int.castRingHom ℝ)
      ((SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F C height) s w hw).val ∘ projection F C height s) = 0 := by
  let z := SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F C height) s w hw
  have HR := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F C height) s hs z.val).mp z.property
  have HE := (FlatAffineEndpointFiniteProjection.equations F height s z.val HR).2.2 0
  have H := FlatAffineShiftPrefixInput.roots_prefix F height (original s) hold
    (FlatAffineEndpointFiniteProjection.sample F s z.val) (FlatAffineEndpointFiniteProjection.copy F s z.val 0)
    (fun i => HE i)
  exact H

theorem value_valid (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hold : (height (original s)).val < FlatAffineFullSourceTower.count F (original s))
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F C height) s w) :
    SquareSampleCompleteVertices.Valid (target F C height) s (value F C height (pair s w)) :=
  SquareSampleProjectionChoice.value_valid_at (FlatAffineEndpointFiniteSample.input F C height) (target F C height)
    (targetComplete F C height) (projection F C height) s w hw (projects F C height s w hs hold hw)

theorem value_point (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hold : (height (original s)).val < FlatAffineFullSourceTower.count F (original s))
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F C height) s w) :
    (SquareSampleCompleteVertices.candidate (target F C height) s (value F C height (pair s w))
      (value_valid F C height s w hs hold hw)).val =
      FlatAffineEndpointFiniteProjection.copy F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F C height) s w hw).val 0 ∘
        FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height) (FlatAffineShiftPrefixInput.depth_le F height) (original s) :=
  SquareSampleProjectionChoice.value_point_at (FlatAffineEndpointFiniteSample.input F C height) (target F C height)
    (targetComplete F C height) (projection F C height) s w hw (projects F C height s w hs hold hw)

end LeanCanny.Encoding.FlatAffineJointPrefixChoice
