/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FullSampleParentCoordinates
public import LeanCanny.Encoding.RationalParentFullBlockScaling

/-! # Native next-stage blocks at actual derived children

An actual child now supplies the parent coordinates for the next full-source
block. Every ambient coordinate is retained, not merely the sampled spatial
tuple. The coefficient reader includes all ancestor-coordinate composition
costs. Specialization has a derived positive scale and the exact original
slice semantics. Constructing subsequent child eliminants, selectors, and
descriptors over this generalized interface remains separate.
-/

@[expose] public section
namespace LeanCanny.Encoding.FullSampleNextBlock
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open BoundedFullSampleChildSource (Inputs)
open FullSampleParentCoordinates
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildCoordinates.coordinate
  BoundedCriticalRationalCoordinates.coordinate BoundedCriticalSampleLabels.parameter
  BoundedFullSampleChildCoordinates.parameter

noncomputable def ofChild (F : Inputs) (offset dim : List Bool → ℕ) : RationalParentFullBlock.Inputs where
  parent := ambient F
  source := F.block.source
  offset := offset
  dim := dim

theorem ofChild_access {F : Inputs} (h : F.PolyTime) {offset dim : List Bool → ℕ}
    (ho : BinaryFn offset) (hk : UnaryFn dim) : (ofChild F offset dim).Access :=
  ⟨ambient_access h, h.block.source, ho, hk⟩

theorem coefficient_evaluator {F : Inputs} (h : F.PolyTime) {offset dim : List Bool → ℕ}
    (ho : BinaryFn offset) (hk : UnaryFn dim) :
    SpaceFunction (RationalParentFullBlockPolynomial.coefficient (ofChild F offset dim)) :=
  RationalParentFullBlockPolynomial.evaluator (ofChild_access h ho hk) h.sourceArity

theorem original (F : Inputs) (offset dim : List Bool → ℕ) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (x : BoundedFullSampleChildActualSamples.Samples F u p) :
    RationalParentFullBlockScaling.original (ofChild F offset dim) u (childParameter F u p x).val =
      CoordinateBlockSpecialization.finite (Int.castRingHom ℝ)
        (BoundedCriticalSampleBlockSource.assignment p.val (F.block.offset u) (F.block.dim u)
          (BoundedFullSampleChildActualSamples.point F u p x))
        (offset u) (dim u) (BoundedFullCriticalSamples.polynomial F.block.source u) := by
  have hp := funext (ambient_point F u p x)
  change CoordinateBlockSpecialization.finite (Int.castRingHom ℝ)
    (RationalCoordinateFamily.point (ambient F) u (childParameter F u p x).val)
    (offset u) (dim u) (BoundedFullCriticalSamples.polynomial F.block.source u) = _
  rw [hp]

theorem specialization (F : Inputs) (offset dim : List Bool → ℕ) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (x : BoundedFullSampleChildActualSamples.Samples F u p) :
    0 < RationalParentFullBlockScaling.scale (ofChild F offset dim) u (childParameter F u p x).val ∧
      RationalParentFullBlockScaling.specialized (ofChild F offset dim) u (childParameter F u p x).val =
        MvPolynomial.C (RationalParentFullBlockScaling.scale (ofChild F offset dim) u (childParameter F u p x).val) *
          CoordinateBlockSpecialization.finite (Int.castRingHom ℝ)
            (BoundedCriticalSampleBlockSource.assignment p.val (F.block.offset u) (F.block.dim u)
              (BoundedFullSampleChildActualSamples.point F u p x))
            (offset u) (dim u) (BoundedFullCriticalSamples.polynomial F.block.source u) := by
  refine ⟨RationalParentFullBlockScaling.scale_pos (ofChild F offset dim) u (childParameter F u p x).val
    (ambient_defined F u p x), ?_⟩
  rw [RationalParentFullBlockScaling.specialized_eq (ofChild F offset dim) u (childParameter F u p x).val
    (ambient_defined F u p x), original]
  rfl

theorem compact_level (F : Inputs) (offset dim : List Bool → ℕ) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (x : BoundedFullSampleChildActualSamples.Samples F u p)
    (hfit : offset u + dim u ≤ F.block.source.dim u + 4) (t : ℝ) :
    IsCompact {y : Fin (dim u) → ℝ |
      (CoordinateBlockSpecialization.finite (Int.castRingHom ℝ)
        (BoundedCriticalSampleBlockSource.assignment p.val (F.block.offset u) (F.block.dim u)
          (BoundedFullSampleChildActualSamples.point F u p x))
        (offset u) (dim u) (BoundedFullCriticalSamples.polynomial F.block.source u)).eval y = t} := by
  rw [← original F offset dim u p x]
  exact RationalParentFullBlockScaling.compact_level (ofChild F offset dim) u (childParameter F u p x).val hfit t

end LeanCanny.Encoding.FullSampleNextBlock
