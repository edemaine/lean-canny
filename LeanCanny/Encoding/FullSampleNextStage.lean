/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FullSampleNextBlock
public import LeanCanny.Encoding.SampleParentParameters
public import LeanCanny.Encoding.RationalParentChildParents

/-! # Generalized child elimination over actual derived samples

The previous child supplies both its native separable parameter equation and
its full ambient rational coordinates. The generalized joint and primitive
pipelines then give a unique parameter for every regular next-stage critical
point. Ancestor coordinates and denominator nonvanishing survive this step.
The direction is still supplied; selection, native filters, descriptors, and
uniform recursion bounds remain to be connected.
-/

@[expose] public section
namespace LeanCanny.Encoding.FullSampleNextStage
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open BoundedFullSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildCoordinates.parameter
  BoundedCriticalSampleLabels.parameter BoundedFullSampleChildCoordinates.coordinate
  RationalParentChildCoordinates.parameter RationalParentChildCoordinates.coordinate

noncomputable def joint (F : Inputs) (offset dim : List Bool → ℕ) : RationalParentJointSource.Inputs :=
  ⟨FullSampleNextBlock.ofChild F offset dim, SampleParentParameters.child F⟩

theorem joint_access {F : Inputs} (h : F.PolyTime) {offset dim : List Bool → ℕ}
    (ho : BinaryFn offset) (hk : UnaryFn dim) : (joint F offset dim).Access :=
  ⟨FullSampleNextBlock.ofChild_access h ho hk, SampleParentParameters.child_access h⟩

noncomputable def child (F : Inputs) (offset dim w : List Bool → ℕ) (bits : List Bool → List Bool)
    (pivot : (u : List Bool) → Fin (dim u)) : RationalParentChildSource.Inputs :=
  ⟨joint F offset dim, w, bits, pivot⟩

theorem child_access {F : Inputs} (h : F.PolyTime) {offset dim w : List Bool → ℕ}
    (ho : BinaryFn offset) (hk : UnaryFn dim) (hw : UnaryFn w) {bits : List Bool → List Bool}
    (E : SpaceFunction bits) (pivot : (u : List Bool) → Fin (dim u))
    (hp : BinaryFn (fun u => (pivot u).val)) : (child F offset dim w bits pivot).Access :=
  ⟨joint_access h ho hk, hw, E, hp, h.sourceArity⟩

theorem sample_complete (F : Inputs) (offset dim w : List Bool → ℕ) (bits : List Bool → List Bool)
    (pivot : (u : List Bool) → Fin (dim u)) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (x : BoundedFullSampleChildActualSamples.Samples F u p) (y : Fin (dim u) → ℝ)
    (hy : ∀ i, (RationalParentChildParameters.originalRows (child F offset dim w bits pivot) u
      (FullSampleParentCoordinates.childParameter F u p x).val i).eval y = 0)
    (hr : (fderiv ℝ (fun z => fun i =>
      (RationalParentChildParameters.originalRows (child F offset dim w bits pivot) u
        (FullSampleParentCoordinates.childParameter F u p x).val i).eval z) y).IsInvertible) :
    ∃! eta : RationalParentChildParameters.RegularParameters (child F offset dim w bits pivot) u,
      RationalParentChildParameters.decode (child F offset dim w bits pivot) u eta.val =
        Fin.cons (FullSampleParentCoordinates.childParameter F u p x).val y :=
  RationalParentChildParameters.sample_complete (child F offset dim w bits pivot) u
    (FullSampleParentCoordinates.childParameter F u p x).val (SampleParentParameters.child_root F u p x)
    (FullSampleParentCoordinates.ambient_defined F u p x) y hy hr

theorem ambient_defined (F : Inputs) (offset dim w : List Bool → ℕ) (bits : List Bool → List Bool)
    (pivot : (u : List Bool) → Fin (dim u)) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (x : BoundedFullSampleChildActualSamples.Samples F u p) (y : Fin (dim u) → ℝ)
    (eta : RationalParentChildParameters.RegularParameters (child F offset dim w bits pivot) u)
    (he : RationalParentChildParameters.decode (child F offset dim w bits pivot) u eta.val =
      Fin.cons (FullSampleParentCoordinates.childParameter F u p x).val y) :
    RationalCoordinateFamily.Defined (RationalParentChildParents.ambient (child F offset dim w bits pivot)) u eta.val := by
  apply RationalParentChildParents.ambient_defined (child F offset dim w bits pivot) u eta.val eta.property.1
  rw [RationalParentChildParents.retained_of_decode (child F offset dim w bits pivot) u eta.val
    (FullSampleParentCoordinates.childParameter F u p x).val y he]
  exact FullSampleParentCoordinates.ambient_defined F u p x

theorem ambient_point (F : Inputs) (offset dim w : List Bool → ℕ) (bits : List Bool → List Bool)
    (pivot : (u : List Bool) → Fin (dim u)) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (x : BoundedFullSampleChildActualSamples.Samples F u p) (y : Fin (dim u) → ℝ)
    (eta : RationalParentChildParameters.RegularParameters (child F offset dim w bits pivot) u)
    (he : RationalParentChildParameters.decode (child F offset dim w bits pivot) u eta.val =
      Fin.cons (FullSampleParentCoordinates.childParameter F u p x).val y) (i : ℕ) :
    RationalCoordinateFamily.point (RationalParentChildParents.ambient (child F offset dim w bits pivot)) u eta.val i =
      if hi : BoundedCriticalSampleBlockSource.InBlock (offset u) (dim u) i then
        y ⟨i - offset u, by unfold BoundedCriticalSampleBlockSource.InBlock at hi; omega⟩
      else BoundedCriticalSampleBlockSource.assignment p.val (F.block.offset u) (F.block.dim u)
        (BoundedFullSampleChildActualSamples.point F u p x) i := by
  rw [RationalParentChildParents.ambient_point (child F offset dim w bits pivot) u eta.val eta.property.1]
  have hr : RationalParentChildParents.retained (child F offset dim w bits pivot) u eta.val =
      (FullSampleParentCoordinates.childParameter F u p x).val := by
    rw [RationalParentChildParents.retained_of_decode (child F offset dim w bits pivot) u eta.val
    (FullSampleParentCoordinates.childParameter F u p x).val y he]
  have hs : RationalParentChildParents.spatialPoint (child F offset dim w bits pivot) u eta.val = y := by
    funext j
    simp only [RationalParentChildParents.spatialPoint, he, Fin.cons_succ]
  rw [hr, hs]
  unfold RationalParentBlockCodes.assignment
  change (if hi : BoundedCriticalSampleBlockSource.InBlock (offset u) (dim u) i then
      y ⟨i - offset u, by unfold BoundedCriticalSampleBlockSource.InBlock at hi; omega⟩
    else RationalCoordinateFamily.point (FullSampleParentCoordinates.ambient F) u
      (FullSampleParentCoordinates.childParameter F u p x).val i) = _
  split_ifs
  · rfl
  · exact FullSampleParentCoordinates.ambient_point F u p x i

end LeanCanny.Encoding.FullSampleNextStage
