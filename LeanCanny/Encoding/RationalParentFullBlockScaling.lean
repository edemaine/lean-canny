/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentFullBlockPolynomial
public import LeanCanny.Encoding.RationalParentBlockEvaluation
public import LeanCanny.Encoding.BoundedFullGeometry
public import LeanCanny.Geometry.CoordinateBlockCompactness
public import LeanCanny.Geometry.ScaledCriticalSystem
public import LeanCanny.Encoding.BoundedCriticalSampleBlockCriticalGeometry

/-! # Exact positive scaling for full-source sample blocks

At every defined rational parent, cleared denominators are constant in the free
coordinates. Specialization is therefore a positive constant times the
original block of the constructed full source. Its complete critical zero
set and analytic regularity are preserved, including singular critical roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentFullBlockScaling
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open RationalParentFullBlock RationalParentFullBlockPolynomial
open RationalParentBlockCodes
open BoundedCriticalSampleBlockSource (environment InBlock)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def scale (F : Inputs) (u : List Bool)
    (theta : ℝ) : ℝ :=
  ∏ i ∈ Finset.range (arity F u), (coordinate F.parent F.offset F.dim false u i).eval₂ (Int.castRingHom ℝ)
    (environment _ theta 0) ^ clearing F u

theorem scale_pos (F : Inputs) (u : List Bool) (theta : ℝ) (hA : RationalCoordinateFamily.Defined F.parent u theta) :
    0 < scale F u theta := by
  unfold scale clearing
  apply Finset.prod_pos
  intro i _
  rw [pow_mul]
  exact pow_pos (sq_pos_of_ne_zero
    (RationalParentBlockCodes.denominator_nonzero F.parent F.offset F.dim u theta hA 0 i)) _

theorem eval (F : Inputs) (u : List Bool) (theta : ℝ) (hA : RationalCoordinateFamily.Defined F.parent u theta)
    (y : Fin (F.dim u) → ℝ) :
    (polynomial F u).eval₂ (Int.castRingHom ℝ)
      (environment _ theta y) =
        scale F u theta * ((family F).source u).eval₂ (Int.castRingHom ℝ)
          (fun i => assignment F.parent F.offset F.dim u theta y i.val) := by
  let v := environment _ theta y
  have H := IndexedMultivariateRational.eval₂_cleared (Int.castRingHom ℝ) v
    (arity F u) ((family F).terms u) (clearing F u) ((family F).coefficient u)
    (FixedWidthPolynomial.entry (sourceWidth F u))
    (coordinate F.parent F.offset F.dim true u) (coordinate F.parent F.offset F.dim false u)
    ((family F).indexed.exponent_le u)
    (fun i _ => RationalParentBlockCodes.denominator_nonzero F.parent F.offset F.dim u theta hA y i)
  have hs : RationalSubstitution.Indexed.source (arity F u) ((family F).terms u) ((family F).coefficient u)
      (FixedWidthPolynomial.entry (sourceWidth F u)) = (family F).source u := (family F).source_eq u
  rw [hs] at H
  have hp : (∏ i ∈ Finset.range (arity F u), (coordinate F.parent F.offset F.dim false u i).eval₂
      (Int.castRingHom ℝ) v ^ clearing F u) = scale F u theta := by
    unfold scale
    apply Finset.prod_congr rfl
    intro i _
    rw [RationalParentBlockCodes.denominator_constant F.parent F.offset F.dim u theta y 0 i]
  rw [hp] at H
  have hv : (fun i : Fin (arity F u) => (coordinate F.parent F.offset F.dim true u i.val).eval₂ (Int.castRingHom ℝ) v /
      (coordinate F.parent F.offset F.dim false u i.val).eval₂ (Int.castRingHom ℝ) v) =
        (fun i => assignment F.parent F.offset F.dim u theta y i.val) :=
    funext fun i => RationalParentBlockCodes.coordinate_eval F.parent F.offset F.dim u theta y i.val
  rw [hv] at H
  exact H

noncomputable def original (F : Inputs) (u : List Bool)
    (theta : ℝ) : MvPolynomial (Fin (F.dim u)) ℝ :=
  CoordinateBlockSpecialization.finite (Int.castRingHom ℝ) (RationalCoordinateFamily.point F.parent u theta) (F.offset u) (F.dim u) ((family F).source u)

theorem eval_original (F : Inputs) (u : List Bool) (theta : ℝ)
    (y : Fin (F.dim u) → ℝ) : (original F u theta).eval y =
      ((family F).source u).eval₂ (Int.castRingHom ℝ) (fun i => assignment F.parent F.offset F.dim u theta y i.val) := by
  unfold original
  rw [CoordinateBlockSpecialization.eval_finite]
  congr 1
  funext i
  simp only [assignment, InBlock]
  by_cases hi : F.offset u ≤ i.val ∧ i.val < F.offset u + F.dim u
  · simp only [dite_eq_left hi]
  · simp only [dite_eq_right hi]

noncomputable def specialized (F : Inputs) (u : List Bool)
    (theta : ℝ) : MvPolynomial (Fin (F.dim u)) ℝ :=
  ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ)
    theta (polynomial F u)

theorem specialized_eq (F : Inputs) (u : List Bool) (theta : ℝ) (hA : RationalCoordinateFamily.Defined F.parent u theta) :
    specialized F u theta = C (scale F u theta) * original F u theta := by
  apply MvPolynomial.funext
  intro y
  rw [specialized, ParameterSpatialSpecialization.eval_specialize,
    ← BoundedCriticalSampleBlockCriticalGeometry.environment_eq_cons, eval F u theta hA, eval_mul, eval_C, eval_original]

theorem zero_iff (F : Inputs) (u : List Bool) (theta : ℝ) (hA : RationalCoordinateFamily.Defined F.parent u theta)
    (y : Fin (F.dim u) → ℝ) : (specialized F u theta).eval y = 0 ↔ (original F u theta).eval y = 0 := by
  rw [specialized_eq F u theta hA, eval_mul, eval_C]
  simp only [mul_eq_zero, ne_of_gt (scale_pos F u theta hA), false_or]

theorem hypersurface_regular_iff (F : Inputs) (u : List Bool) (theta : ℝ) (hA : RationalCoordinateFamily.Defined F.parent u theta)
    (y : Fin (F.dim u) → ℝ) :
    Function.Surjective (fderiv ℝ (fun z => (specialized F u theta).eval z) y) ↔
      Function.Surjective (fderiv ℝ (fun z => (original F u theta).eval z) y) := by
  rw [specialized_eq F u theta hA]
  simpa only [eval₂_id] using Geometry.ScaledCriticalSystem.hypersurface_regular_iff (RingHom.id ℝ)
    (original F u theta) (scale F u theta) (ne_of_gt (scale_pos F u theta hA)) y

theorem critical_zero_iff (F : Inputs) (u : List Bool) (theta : ℝ) (hA : RationalCoordinateFamily.Defined F.parent u theta)
    (b : Fin (F.dim u)) (v : Fin (F.dim u) → ℝ) (y : Fin (F.dim u) → ℝ) :
    (∀ i, (ProjectionCriticalFamily.spatialEquation (specialized F u theta) b v i).eval y = 0) ↔
      ∀ i, (ProjectionCriticalFamily.spatialEquation (original F u theta) b v i).eval y = 0 := by
  rw [specialized_eq F u theta hA]
  exact Geometry.ScaledCriticalSystem.zero_iff (RingHom.id ℝ) _ b v _ (ne_of_gt (scale_pos F u theta hA)) y

theorem critical_regular_iff (F : Inputs) (u : List Bool) (theta : ℝ) (hA : RationalCoordinateFamily.Defined F.parent u theta)
    (b : Fin (F.dim u)) (v : Fin (F.dim u) → ℝ) (y : Fin (F.dim u) → ℝ) :
    (fderiv ℝ (fun z => fun i => (ProjectionCriticalFamily.spatialEquation (specialized F u theta) b v i).eval z) y).IsInvertible ↔
      (fderiv ℝ (fun z => fun i => (ProjectionCriticalFamily.spatialEquation (original F u theta) b v i).eval z) y).IsInvertible := by
  rw [specialized_eq F u theta hA]
  simpa only [eval₂_id] using Geometry.ScaledCriticalSystem.regular_iff (RingHom.id ℝ) _ b v (scale F u theta)
    (ne_of_gt (scale_pos F u theta hA)) y

theorem proper_original (F : Inputs) (u : List Bool) (theta : ℝ)
    (hfit : F.offset u + F.dim u ≤ F.source.dim u + 4) :
    IsProperMap (fun y : Fin (F.dim u) → ℝ => (original F u theta).eval y) := by
  unfold original
  apply Geometry.CoordinateBlockCompactness.proper_finite (Int.castRingHom ℝ)
    (RationalCoordinateFamily.point F.parent u theta) (F.offset u) (F.dim u) ((family F).source u) hfit
  exact BoundedFullGeometry.proper (BoundedFullWriter.original F.source u)
    (BoundedFullWriter.size F.source u) (BoundedFullWriter.size F.source u) (F.source.radius u)

theorem compact_level (F : Inputs) (u : List Bool) (theta : ℝ)
    (hfit : F.offset u + F.dim u ≤ F.source.dim u + 4) (t : ℝ) :
    IsCompact {y : Fin (F.dim u) → ℝ | (original F u theta).eval y = t} :=
  (proper_original F u theta hfit).isCompact_preimage isCompact_singleton

end LeanCanny.Encoding.RationalParentFullBlockScaling
