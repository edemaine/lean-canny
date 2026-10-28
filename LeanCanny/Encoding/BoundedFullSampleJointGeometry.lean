/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleJointCoefficient
public import LeanCanny.Geometry.RegularAffineSubsetCount

/-! # Joint roots over the actual full-source parent samples

The retained parameter row and positive denominator clearing preserve every
critical root of the original coordinate block. At a parent parameter,
joint regularity is equivalent to regularity of that original critical
system. Regular candidates have native finite label bounds even when other
parent fibers contain singular or positive-dimensional sets.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleJointGeometry
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open BoundedFullSampleBlock BoundedFullSampleJointSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter
  BoundedFullSampleBlockPolynomial.polynomial BoundedFullSampleBlockCriticalSource.polynomial

noncomputable def spatial (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (b : Fin (F.dim u)) (t : ℝ) : Fin (F.dim u) → MvPolynomial (Fin (F.dim u)) ℝ :=
  ProjectionCriticalFamily.spatialEquation
    (ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ) t
      (BoundedFullSampleBlockPolynomial.polynomial F u)) b
    (fun j => (BoundedFullSampleBlockCriticalSource.direction F.dim w bits u j : ℝ))

theorem root_iff (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (b : Fin (F.dim u)) (t : ℝ) (y : Fin (F.dim u) → ℝ) :
    (∀ i, (system F w bits u b i).eval₂ (Int.castRingHom ℝ) (Fin.cons t y) = 0) ↔
      (BoundedCriticalRationalCoordinates.parameter F.parent (pairFst u)).eval₂ (Int.castRingHom ℝ) t = 0 ∧
        ∀ i, (spatial F w bits u b t i).eval y = 0 := by
  rw [system, RetainedParameterSystem.zero_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  rw [← ParameterSpatialSpecialization.eval_specialize,
    BoundedFullSampleBlockCriticalSource.specialize_polynomial]
  rfl

theorem regular_at_parameter_root (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (b : Fin (F.dim u)) (t : ℝ) (y : Fin (F.dim u) → ℝ)
    (ht : (BoundedCriticalRationalCoordinates.parameter F.parent (pairFst u)).eval₂ (Int.castRingHom ℝ) t = 0) :
    (fderiv ℝ (fun z => fun i => (system F w bits u b i).eval₂ (Int.castRingHom ℝ) z)
      (Fin.cons t y)).IsInvertible ↔
        (fderiv ℝ (fun z => fun i => (spatial F w bits u b t i).eval z) y).IsInvertible := by
  have H := RetainedParameterSystem.regular_iff (BoundedCriticalRationalCoordinates.parameter F.parent (pairFst u))
    (fun i => BoundedFullSampleBlockCriticalSource.polynomial F w bits u b i) t y
    (BoundedCriticalRationalCoordinates.parameter_derivative_ne_zero F.parent (pairFst u) t ht)
  simpa only [system, spatial, BoundedFullSampleBlockCriticalSource.specialize_polynomial] using H

theorem sample_root_iff (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (b : Fin (F.dim u)) (y : Fin (F.dim u) → ℝ) :
    (∀ i, (system F w bits u b i).eval₂ (Int.castRingHom ℝ)
      (Fin.cons (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val y) = 0) ↔
        ∀ i, (ProjectionCriticalFamily.spatialEquation (BoundedFullSampleBlockScaling.original F u p) b
          (fun j => (BoundedFullSampleBlockCriticalSource.direction F.dim w bits u j : ℝ)) i).eval y = 0 := by
  have ht := ((BoundedCriticalSampleLabels.mem_rootSet F.parent (pairFst u) _).mp
    (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).property).1
  rw [root_iff, and_iff_right ht]
  exact BoundedFullSampleBlockScaling.critical_zero_iff F u p b _ y

theorem sample_regular_iff (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (b : Fin (F.dim u)) (y : Fin (F.dim u) → ℝ) :
    (fderiv ℝ (fun z => fun i => (system F w bits u b i).eval₂ (Int.castRingHom ℝ) z)
      (Fin.cons (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val y)).IsInvertible ↔
        (fderiv ℝ (fun z => fun i =>
          (ProjectionCriticalFamily.spatialEquation (BoundedFullSampleBlockScaling.original F u p) b
            (fun j => (BoundedFullSampleBlockCriticalSource.direction F.dim w bits u j : ℝ)) i).eval z) y).IsInvertible := by
  have ht := ((BoundedCriticalSampleLabels.mem_rootSet F.parent (pairFst u) _).mp
    (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).property).1
  rw [regular_at_parameter_root F w bits u b _ y ht]
  exact BoundedFullSampleBlockScaling.critical_regular_iff F u p b _ y

abbrev RegularCandidates (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (b : Fin (F.dim u)) :=
  Geometry.RegularAffineRootCount.RegularRoots (system F w bits u b)

theorem finite_regular_candidates (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (b : Fin (F.dim u)) :
    Finite (RegularCandidates F w bits u b) ∧
      Nat.card (RegularCandidates F w bits u b) ≤ 2 ^ labelWidth F u :=
  Geometry.RegularAffineRootCount.finite_regular_card_le_uniform (system F w bits u b) (degree F u)
    (polynomial_degree F w bits u b) (degree_pos F u)

theorem regular_candidate_at_sample (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (b : Fin (F.dim u)) (y : Fin (F.dim u) → ℝ)
    (hy : ∀ i, (ProjectionCriticalFamily.spatialEquation (BoundedFullSampleBlockScaling.original F u p) b
      (fun j => (BoundedFullSampleBlockCriticalSource.direction F.dim w bits u j : ℝ)) i).eval y = 0)
    (hr : (fderiv ℝ (fun z => fun i =>
      (ProjectionCriticalFamily.spatialEquation (BoundedFullSampleBlockScaling.original F u p) b
        (fun j => (BoundedFullSampleBlockCriticalSource.direction F.dim w bits u j : ℝ)) i).eval z) y).IsInvertible) :
    ∃ z : RegularCandidates F w bits u b,
      z.val.val = Fin.cons (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val y :=
  ⟨⟨⟨_, (sample_root_iff F w bits u p b y).mpr hy⟩, (sample_regular_iff F w bits u p b y).mpr hr⟩, rfl⟩

end LeanCanny.Encoding.BoundedFullSampleJointGeometry
