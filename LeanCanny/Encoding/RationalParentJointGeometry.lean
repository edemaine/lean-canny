/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentJointCoefficient
public import LeanCanny.Geometry.RegularAffineSubsetCount

/-! # Joint roots over defined rational parents

The retained parameter row and positive denominator clearing preserve every
critical root of the original coordinate block. At a parent parameter,
joint regularity is equivalent to regularity of that original critical
system. Regular candidates have native finite label bounds even when other
parent fibers contain singular or positive-dimensional sets.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentJointGeometry
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open RationalParentJointSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentFullBlockPolynomial.polynomial RationalParentFullBlockCriticalSource.polynomial

noncomputable def spatial (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (b : Fin (F.block.dim u)) (t : ℝ) : Fin (F.block.dim u) → MvPolynomial (Fin (F.block.dim u)) ℝ :=
  ProjectionCriticalFamily.spatialEquation
    (ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ) t
      (RationalParentFullBlockPolynomial.polynomial F.block u)) b
    (fun j => (RationalParentFullBlockCriticalSource.direction F.block.dim w bits u j : ℝ))

theorem root_iff (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (b : Fin (F.block.dim u)) (t : ℝ) (y : Fin (F.block.dim u) → ℝ) :
    (∀ i, (system F w bits u b i).eval₂ (Int.castRingHom ℝ) (Fin.cons t y) = 0) ↔
      (F.parent.polynomial u).eval₂ (Int.castRingHom ℝ) t = 0 ∧
        ∀ i, (spatial F w bits u b t i).eval y = 0 := by
  rw [system, RetainedParameterSystem.zero_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  rw [← ParameterSpatialSpecialization.eval_specialize,
    RationalParentFullBlockCriticalSource.specialize_polynomial]
  rfl

theorem regular_at_parameter_root (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (b : Fin (F.block.dim u)) (t : ℝ) (y : Fin (F.block.dim u) → ℝ)
    (ht : (F.parent.polynomial u).eval₂ (Int.castRingHom ℝ) t = 0) :
    (fderiv ℝ (fun z => fun i => (system F w bits u b i).eval₂ (Int.castRingHom ℝ) z)
      (Fin.cons t y)).IsInvertible ↔
        (fderiv ℝ (fun z => fun i => (spatial F w bits u b t i).eval z) y).IsInvertible := by
  have H := RetainedParameterSystem.regular_iff (F.parent.polynomial u)
    (fun i => RationalParentFullBlockCriticalSource.polynomial F.block w bits u b i) t y
    (SeparablePolynomialFamily.derivative_ne_zero F.parent u t ht)
  simpa only [system, spatial, RationalParentFullBlockCriticalSource.specialize_polynomial] using H

theorem original_root_iff (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (theta : ℝ) (ht : (F.parent.polynomial u).eval₂ (Int.castRingHom ℝ) theta = 0)
    (hA : RationalCoordinateFamily.Defined F.block.parent u theta)
    (b : Fin (F.block.dim u)) (y : Fin (F.block.dim u) → ℝ) :
    (∀ i, (system F w bits u b i).eval₂ (Int.castRingHom ℝ) (Fin.cons theta y) = 0) ↔
      ∀ i, (ProjectionCriticalFamily.spatialEquation (RationalParentFullBlockScaling.original F.block u theta) b
        (fun j => (RationalParentFullBlockCriticalSource.direction F.block.dim w bits u j : ℝ)) i).eval y = 0 := by
  rw [root_iff, and_iff_right ht]
  exact RationalParentFullBlockScaling.critical_zero_iff F.block u theta hA b _ y

theorem original_regular_iff (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (theta : ℝ) (ht : (F.parent.polynomial u).eval₂ (Int.castRingHom ℝ) theta = 0)
    (hA : RationalCoordinateFamily.Defined F.block.parent u theta)
    (b : Fin (F.block.dim u)) (y : Fin (F.block.dim u) → ℝ) :
    (fderiv ℝ (fun z => fun i => (system F w bits u b i).eval₂ (Int.castRingHom ℝ) z)
      (Fin.cons theta y)).IsInvertible ↔
      (fderiv ℝ (fun z => fun i =>
        (ProjectionCriticalFamily.spatialEquation (RationalParentFullBlockScaling.original F.block u theta) b
          (fun j => (RationalParentFullBlockCriticalSource.direction F.block.dim w bits u j : ℝ)) i).eval z) y).IsInvertible := by
  rw [regular_at_parameter_root F w bits u b theta y ht]
  exact RationalParentFullBlockScaling.critical_regular_iff F.block u theta hA b _ y

abbrev RegularCandidates (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (b : Fin (F.block.dim u)) :=
  Geometry.RegularAffineRootCount.RegularRoots (system F w bits u b)

theorem finite_regular_candidates (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (b : Fin (F.block.dim u)) :
    Finite (RegularCandidates F w bits u b) ∧
      Nat.card (RegularCandidates F w bits u b) ≤ 2 ^ labelWidth F u :=
  Geometry.RegularAffineRootCount.finite_regular_card_le_uniform (system F w bits u b) (degree F u)
    (polynomial_degree F w bits u b) (degree_pos F u)

theorem regular_candidate_at_parent (F : Inputs) (w : List Bool → ℕ) (bits : List Bool → List Bool)
    (u : List Bool) (theta : ℝ) (ht : (F.parent.polynomial u).eval₂ (Int.castRingHom ℝ) theta = 0)
    (hA : RationalCoordinateFamily.Defined F.block.parent u theta)
    (b : Fin (F.block.dim u)) (y : Fin (F.block.dim u) → ℝ)
    (hy : ∀ i, (ProjectionCriticalFamily.spatialEquation (RationalParentFullBlockScaling.original F.block u theta) b
      (fun j => (RationalParentFullBlockCriticalSource.direction F.block.dim w bits u j : ℝ)) i).eval y = 0)
    (hr : (fderiv ℝ (fun z => fun i =>
      (ProjectionCriticalFamily.spatialEquation (RationalParentFullBlockScaling.original F.block u theta) b
        (fun j => (RationalParentFullBlockCriticalSource.direction F.block.dim w bits u j : ℝ)) i).eval z) y).IsInvertible) :
    ∃ z : RegularCandidates F w bits u b, z.val.val = Fin.cons theta y :=
  ⟨⟨⟨_, (original_root_iff F w bits u theta ht hA b y).mpr hy⟩,
    (original_regular_iff F w bits u theta ht hA b y).mpr hr⟩, rfl⟩

end LeanCanny.Encoding.RationalParentJointGeometry
