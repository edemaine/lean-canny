/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.CriticalSampleChildPairs
public import LeanCanny.Encoding.BoundedCriticalSampleBlockScaling

/-! # Child-sample connectivity for the original frozen-coordinate term

The native pair scan retains its constructed descriptors and parent filter.
Its geometric assumptions and recursive path predicate can now refer to the
original term on the actual slice. Constant denominator scaling transports
both hypersurface regularity and every critical root, including singular ones.
The recursive path procedure and good-direction construction remain separate.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CriticalSampleOriginalSlice
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding LeanCanny.ETR MvPolynomial
open BoundedCriticalSampleChildSource (Inputs)
open BoundedCriticalSampleChildActualSamples
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleBlockScaling.scale
  BoundedCriticalSampleBlockScaling.original BoundedCriticalSampleLabels.parameter

noncomputable def polynomial (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :=
  BoundedCriticalSampleBlockScaling.original (TermView.term (F.term u)) p.val (F.offset u) (F.dim u)

noncomputable def space (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) : Set (Fin (F.dim u) → ℝ) :=
  {y | (TermView.term (F.term u)).eval
    (BoundedCriticalSampleBlockSource.assignment p.val (F.offset u) (F.dim u) y) = 0}

theorem zero_iff (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (y : Fin (F.dim u) → ℝ) :
    (CriticalSampleChildCoverage.polynomial F u p).eval y = 0 ↔ y ∈ space F u p := by
  change (BoundedCriticalSampleBlockScaling.specialized F.parent F.term F.offset F.dim u p).eval y = 0 ↔ _
  rw [BoundedCriticalSampleBlockScaling.specialized_eq, eval_mul, eval_C]
  simp only [mul_eq_zero, ne_of_gt (BoundedCriticalSampleBlockScaling.scale_pos F.parent F.term F.offset F.dim u p),
    false_or, BoundedCriticalSampleBlockScaling.eval_original, space, Set.mem_ofPred_eq]

theorem zero_set (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :
    {y | (CriticalSampleChildCoverage.polynomial F u p).eval y = 0} = space F u p :=
  Set.ext (zero_iff F u p)

theorem regular_iff (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (y : Fin (F.dim u) → ℝ) :
    Function.Surjective (fderiv ℝ (fun z => (CriticalSampleChildCoverage.polynomial F u p).eval z) y) ↔
      Function.Surjective (fderiv ℝ (fun z => (polynomial F u p).eval z) y) := by
  change Function.Surjective (fderiv ℝ
    (fun z => (BoundedCriticalSampleBlockScaling.specialized F.parent F.term F.offset F.dim u p).eval z) y) ↔ _
  rw [BoundedCriticalSampleBlockScaling.specialized_eq]
  simpa only [eval₂_id, polynomial] using Geometry.ScaledCriticalSystem.hypersurface_regular_iff
    (RingHom.id ℝ) (polynomial F u p) (BoundedCriticalSampleBlockScaling.scale F.parent F.term F.offset F.dim u p)
    (ne_of_gt (BoundedCriticalSampleBlockScaling.scale_pos F.parent F.term F.offset F.dim u p)) y

theorem critical_regular_iff (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :
    (∀ y, (∀ i, (spatial F u p i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (spatial F u p i).eval z) y).IsInvertible) ↔
    ∀ y, (∀ i, (ProjectionCriticalFamily.spatialEquation (polynomial F u p)
      (F.pivot u) (CriticalSampleChildCoverage.direction F u) i).eval y = 0) →
        (fderiv ℝ (fun z => fun i => (ProjectionCriticalFamily.spatialEquation (polynomial F u p)
          (F.pivot u) (CriticalSampleChildCoverage.direction F u) i).eval z) y).IsInvertible := by
  simp only [CriticalSampleChildCoverage.spatial_eq]
  apply forall_congr'
  intro y
  exact imp_congr
    (BoundedCriticalSampleBlockScaling.critical_zero_iff F.parent F.term F.offset F.dim u p
      (F.pivot u) (CriticalSampleChildCoverage.direction F u) y)
    (BoundedCriticalSampleBlockScaling.critical_regular_iff F.parent F.term F.offset F.dim u p
      (F.pivot u) (CriticalSampleChildCoverage.direction F u) y)

theorem preconnected_iff (F : Inputs) (L : Language) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (hv : CriticalSampleChildCoverage.direction F u (F.pivot u) = 1)
    (hcompact : IsCompact (space F u p))
    (hregular : ∀ y ∈ space F u p, Function.Surjective (fderiv ℝ (fun z => (polynomial F u p).eval z) y))
    (hcritical : ∀ y, (∀ i, (ProjectionCriticalFamily.spatialEquation (polynomial F u p)
      (F.pivot u) (CriticalSampleChildCoverage.direction F u) i).eval y = 0) →
        (fderiv ℝ (fun z => fun i => (ProjectionCriticalFamily.spatialEquation (polynomial F u p)
          (F.pivot u) (CriticalSampleChildCoverage.direction F u) i).eval z) y).IsInvertible)
    (hL : ∀ x y : Samples F u p,
      pair (pair u (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p))
        (pair (word F u p x) (word F u p y)) ∈ L ↔
          JoinedIn (space F u p) (point F u p x) (point F u p y)) :
    pair u (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p) ∈
      CriticalSampleChildPairs.language F L ↔ IsPreconnected (space F u p) := by
  have hs := zero_set F u p
  have hc : IsCompact {y | (CriticalSampleChildCoverage.polynomial F u p).eval y = 0} := hs.symm ▸ hcompact
  have hr : ∀ y, (CriticalSampleChildCoverage.polynomial F u p).eval y = 0 →
      Function.Surjective (fderiv ℝ (fun z => (CriticalSampleChildCoverage.polynomial F u p).eval z) y) := by
    intro y hy
    exact (regular_iff F u p y).mpr (hregular y ((zero_iff F u p y).mp hy))
  have H := CriticalSampleChildPairs.preconnected_iff F L u p hv hc hr
    ((critical_regular_iff F u p).mpr hcritical) (by simpa only [hs] using hL)
  simpa only [hs] using H

end LeanCanny.Connectivity.CriticalSampleOriginalSlice
