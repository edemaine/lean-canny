/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildCoordinates

/-! # Exact parameter encodings of regular child candidates

The joint equations and Jacobian condition select precisely the regular
candidates among the child parameter roots. The correspondence is bijective,
including when there are no regular candidates. Native equation and
regularity filters are supplied by the downstream child-count modules;
selection of the actual parent root remains a separate obligation.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildParameters
open LeanCanny.Algebra LeanCanny.Geometry
open BoundedFullSampleChildSource (Inputs)
open BoundedFullSampleChildCoordinates (parameter coordinate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleJointSource.system parameter coordinate

noncomputable def decode (F : Inputs) (u : List Bool) (theta : ℝ) :
    Fin (BoundedFullSampleChildSource.count F u) → ℝ :=
  fun i => (coordinate F (pair u (BinaryNatCode.encode i.val))).eval theta

noncomputable def system (F : Inputs) (u : List Bool) :=
  BoundedFullSampleJointSource.system F.block F.directionWidth F.direction u (F.pivot u)

abbrev Candidates (F : Inputs) (u : List Bool) :=
  BoundedFullSampleJointGeometry.RegularCandidates F.block F.directionWidth F.direction u (F.pivot u)

def RegularParameters (F : Inputs) (u : List Bool) :=
  {theta : ℝ // (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0 ∧
    (∀ i, (system F u i).eval₂ (Int.castRingHom ℝ) (decode F u theta) = 0) ∧
    (fderiv ℝ (fun z => fun i => (system F u i).eval₂ (Int.castRingHom ℝ) z) (decode F u theta)).IsInvertible}

noncomputable def candidate (F : Inputs) (u : List Bool) (theta : RegularParameters F u) : Candidates F u :=
  ⟨⟨decode F u theta.val, theta.property.2.1⟩, theta.property.2.2⟩

theorem candidate_injective (F : Inputs) (u : List Bool) : Function.Injective (candidate F u) := by
  intro theta theta' he
  apply Subtype.ext
  apply BoundedFullSampleChildCoordinates.parameter_roots_ext F u theta.val theta'.val theta.property.1 theta'.property.1
  intro i
  exact congrFun (congrArg (fun z : Candidates F u => z.val.val) he) i

theorem candidate_surjective (F : Inputs) (u : List Bool) : Function.Surjective (candidate F u) := by
  intro z
  obtain ⟨theta, ht, hx⟩ := BoundedFullSampleChildCoordinates.regular_candidate_complete F u z
  have he : decode F u theta = z.val.val := funext fun i => (hx i).2
  have hz : ∀ i, (system F u i).eval₂ (Int.castRingHom ℝ) (decode F u theta) = 0 := by
    rw [he]
    exact z.val.property
  have hr : (fderiv ℝ (fun y => fun i => (system F u i).eval₂ (Int.castRingHom ℝ) y)
      (decode F u theta)).IsInvertible := by rw [he]; exact z.property
  refine ⟨⟨theta, ht, hz, hr⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact he

noncomputable def regularEquiv (F : Inputs) (u : List Bool) : RegularParameters F u ≃ Candidates F u :=
  Equiv.ofBijective (candidate F u) ⟨candidate_injective F u, candidate_surjective F u⟩

theorem finite_regular_parameters (F : Inputs) (u : List Bool) :
    Finite (RegularParameters F u) ∧ Nat.card (RegularParameters F u) ≤
      2 ^ BoundedFullSampleJointSource.labelWidth F.block u := by
  have H := BoundedFullSampleJointGeometry.finite_regular_candidates F.block F.directionWidth
    F.direction u (F.pivot u)
  let _ : Finite (Candidates F u) := H.1
  exact ⟨Finite.of_injective (candidate F u) (candidate_injective F u),
    (Nat.card_congr (regularEquiv F u)).trans_le H.2⟩

/-- Critical equations of the original full-source block at an actual parent. -/
noncomputable def originalRows (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) :=
  ProjectionCriticalFamily.spatialEquation (BoundedFullSampleBlockScaling.original F.block u p) (F.pivot u)
    (fun j => (BoundedFullSampleBlockCriticalSource.direction F.block.dim F.directionWidth F.direction u j : ℝ))

/-- The original block's regular critical points have unique child parameters
with the retained parent coordinate and every spatial coordinate intact. -/
theorem sample_complete (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (y : Fin (F.block.dim u) → ℝ)
    (hy : ∀ i, (originalRows F u p i).eval y = 0)
    (hr : (fderiv ℝ (fun z => fun i => (originalRows F u p i).eval z) y).IsInvertible) :
    ∃! theta : RegularParameters F u,
      decode F u theta.val = Fin.cons (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) p).val y := by
  obtain ⟨z, hz⟩ := BoundedFullSampleJointGeometry.regular_candidate_at_sample
    F.block F.directionWidth F.direction u p (F.pivot u) y hy hr
  obtain ⟨theta, htheta⟩ := candidate_surjective F u z
  have hdecode : decode F u theta.val =
      Fin.cons (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) p).val y :=
    (congrArg (fun a : Candidates F u => a.val.val) htheta).trans hz
  refine ⟨theta, hdecode, ?_⟩
  intro theta' htheta'
  apply Subtype.ext
  apply BoundedFullSampleChildCoordinates.parameter_roots_ext F u theta'.val theta.val theta'.property.1 theta.property.1
  intro i
  exact congrFun (htheta'.trans hdecode.symm) i

theorem sample_iff (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (y : Fin (F.block.dim u) → ℝ) :
    (∃ theta : RegularParameters F u,
      decode F u theta.val = Fin.cons (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) p).val y) ↔
        (∀ i, (originalRows F u p i).eval y = 0) ∧
          (fderiv ℝ (fun z => fun i => (originalRows F u p i).eval z) y).IsInvertible := by
  constructor
  · rintro ⟨theta, htheta⟩
    have hz : ∀ i, (BoundedFullSampleJointSource.system F.block F.directionWidth F.direction u (F.pivot u) i).eval₂
        (Int.castRingHom ℝ) (Fin.cons (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) p).val y) = 0 := by
      rw [← htheta]
      exact theta.property.2.1
    have hr : (fderiv ℝ (fun z => fun i =>
        (BoundedFullSampleJointSource.system F.block F.directionWidth F.direction u (F.pivot u) i).eval₂
          (Int.castRingHom ℝ) z)
        (Fin.cons (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) p).val y)).IsInvertible := by
      rw [← htheta]
      exact theta.property.2.2
    exact ⟨(BoundedFullSampleJointGeometry.sample_root_iff F.block F.directionWidth F.direction u p (F.pivot u) y).mp hz,
      (BoundedFullSampleJointGeometry.sample_regular_iff F.block F.directionWidth F.direction u p (F.pivot u) y).mp hr⟩
  · rintro ⟨hy, hr⟩
    exact (sample_complete F u p y hy hr).exists

end LeanCanny.Encoding.BoundedFullSampleChildParameters
