/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineJointPrefixChoice

/-! # Computing frozen ancestor words of current and endpoint joint copies

Each of the three copies satisfies the shifted tower at its own parameter.
Projection drops the varied stage and gives a complete ordinary ancestor
word. Endpoint copies need not share the current copy's parent unless an
incidence test has established that they belong to the same branch.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineJointCopyPrefixChoice
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineJointPrefixChoice (original target targetAccess targetComplete indexAt index_unary prepare prepare_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

noncomputable def projection (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (k : Fin 3) (s : List Bool)
    (i : Fin ((target F C height).count s)) : Fin ((FlatAffineEndpointFiniteSample.input F C height).count s) :=
  FlatAffineEndpointFiniteProjection.slot F s k (FlatAffinePowerPrefix.projection F
    (FlatAffineShiftPrefixInput.depth F height) (FlatAffineShiftPrefixInput.depth_le F height) (original s) i)

theorem coordinate_val (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (k : Fin 3) (s d : List Bool) :
    (SquareSampleProjectedThom.coordinate (FlatAffineEndpointFiniteSample.input F C height) (target F C height)
      (projection F C height k) s d).val = indexAt F C height (original s) d + count F (original s) * k.val + 2 := by
  unfold indexAt SquareSampleProjectedThom.coordinate projection
  rw [FlatAffineEndpointFiniteProjection.slot_val]
  rfl

attribute [local irreducible] FlatAffineJointPrefixChoice.indexAt

theorem coordinate_unary {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (k : Fin 3) :
    UnaryFn (fun q => (SquareSampleProjectedThom.coordinate (FlatAffineEndpointFiniteSample.input F C height)
      (target F C height) (projection F C height k) (pairFst q) (pairSnd q)).val) := by
  have A := (index_unary hF C height hh).comp prepare_FP
  have N := ((FlatAffineFullSourcePositive.count_unary hF).comp FlatAffineJointPrefixChoice.original_FP).comp pairFst_mem_FP
  apply ((A.add (N.mul (UnaryFn.const k.val))).add (UnaryFn.const 2)).of_eq
  intro q
  simp only [prepare, pairFst_pair, pairSnd_pair]
  exact (coordinate_val F C height k (pairFst q) (pairSnd q)).symm

noncomputable def value (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (k : Fin 3) : List Bool → List Bool :=
  SquareSampleProjectionChoice.value (FlatAffineEndpointFiniteSample.input F C height) (target F C height) (projection F C height k)

theorem evaluator {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (k : Fin 3) :
    SpaceFunction (value F C height k) :=
  SquareSampleProjectionChoice.evaluator (FlatAffineEndpointFiniteSample.sampleAccess hF C height hh)
    (targetAccess hF C height hh) (projection F C height k) (coordinate_unary hF C height hh k)

theorem projects (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (k : Fin 3) (s w : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hold : (height (original s)).val < FlatAffineFullSourceTower.count F (original s))
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F C height) s w) :
    ∀ i, ((target F C height).system s i).eval₂ (Int.castRingHom ℝ)
      ((SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F C height) s w hw).val ∘ projection F C height k s) = 0 := by
  let z := SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F C height) s w hw
  have HR := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F C height) s hs z.val).mp z.property
  have HE := (FlatAffineEndpointFiniteProjection.equations F height s z.val HR).2.2 k
  exact FlatAffineShiftPrefixInput.roots_prefix F height (original s) hold
    (if k = 0 then FlatAffineEndpointFiniteProjection.sample F s z.val else FlatAffineEndpointFiniteProjection.endpoint F s z.val)
    (FlatAffineEndpointFiniteProjection.copy F s z.val k) (fun i => HE i)

theorem value_valid (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (k : Fin 3) (s w : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hold : (height (original s)).val < FlatAffineFullSourceTower.count F (original s))
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F C height) s w) :
    SquareSampleCompleteVertices.Valid (target F C height) s (value F C height k (pair s w)) :=
  SquareSampleProjectionChoice.value_valid_at (FlatAffineEndpointFiniteSample.input F C height) (target F C height)
    (targetComplete F C height) (projection F C height k) s w hw (projects F C height k s w hs hold hw)

theorem value_point (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (k : Fin 3) (s w : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hold : (height (original s)).val < FlatAffineFullSourceTower.count F (original s))
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F C height) s w) :
    (SquareSampleCompleteVertices.candidate (target F C height) s (value F C height k (pair s w))
      (value_valid F C height k s w hs hold hw)).val =
      FlatAffineEndpointFiniteProjection.copy F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F C height) s w hw).val k ∘
        FlatAffinePowerPrefix.projection F (FlatAffineShiftPrefixInput.depth F height) (FlatAffineShiftPrefixInput.depth_le F height) (original s) :=
  SquareSampleProjectionChoice.value_point_at (FlatAffineEndpointFiniteSample.input F C height) (target F C height)
    (targetComplete F C height) (projection F C height k) s w hw (projects F C height k s w hs hold hw)

end LeanCanny.Encoding.FlatAffineJointCopyPrefixChoice
