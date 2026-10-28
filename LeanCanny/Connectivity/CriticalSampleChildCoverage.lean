/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildActualSamples
public import LeanCanny.Geometry.ComponentCriticalSampling

/-! # Regular child descriptors sample every component of a compact slice

A normalized direction whose spatial critical points are all regular makes
the constructed finite actual-parent samples meet every component of the
compact regular slice. Every point can reach a sample with an accepted short
native descriptor. Constructing such directions in native space is separate.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CriticalSampleChildCoverage
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding LeanCanny.Geometry
open BoundedCriticalSampleChildSource (Inputs)
open BoundedCriticalSampleChildActualSamples
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleBlockTerm.polynomial
  BoundedCriticalSampleLabels.parameter

noncomputable def polynomial (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :=
  ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ)
    (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val
    (BoundedCriticalSampleBlockTerm.polynomial F.parent F.term F.offset F.dim u)

noncomputable def direction (F : Inputs) (u : List Bool) (i : Fin (F.dim u)) : ℝ :=
  BoundedCriticalSampleBlockCriticalSource.direction F.dim F.directionWidth F.direction u i

theorem spatial_eq (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :
    spatial F u p = ProjectionCriticalFamily.spatialEquation (polynomial F u p) (F.pivot u) (direction F u) := rfl

theorem exists_joined_sample (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (hv : direction F u (F.pivot u) = 1)
    (hcompact : IsCompact {y | (polynomial F u p).eval y = 0})
    (hregular : ∀ y, (polynomial F u p).eval y = 0 →
      Function.Surjective (fderiv ℝ (fun z => (polynomial F u p).eval z) y))
    (hcritical : ∀ y, (∀ i, (spatial F u p i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (spatial F u p i).eval z) y).IsInvertible)
    (y : Fin (F.dim u) → ℝ) (hy : (polynomial F u p).eval y = 0) :
    ∃ x : Samples F u p,
      JoinedIn {z | (polynomial F u p).eval z = 0} y (point F u p x) ∧
      (word F u p x).length ≤ BoundedCriticalSampleChildHashChoice.descriptorWidth F u ∧
      pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p) (word F u p x)) ∈
        BoundedCriticalSampleChildParentSelection.language F := by
  obtain ⟨z, hj, hz⟩ := ComponentCriticalSampling.exists_joined_critical
    (polynomial F u p) (F.pivot u) (direction F u) hv 0 hcompact hregular y hy
  have hzero : ∀ i, (spatial F u p i).eval z = 0 := by
    rw [spatial_eq]
    apply (ProjectionCriticalFamily.spatial_zero_iff (RingHom.id ℝ) (polynomial F u p)
      (F.pivot u) (direction F u) hv z).mpr
    exact (ProjectionCriticalBranches.value_iff (polynomial F u p) (F.pivot u) (direction F u) hv 0 z).mp hz
  obtain ⟨x, hx⟩ := point_complete F u p z hzero (hcritical z hzero)
  refine ⟨x, ?_, word_length F u p x, word_valid F u p x⟩
  simpa only [hx] using hj

abbrev Level (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :=
  RegularFiber.Fiber (fun y => (polynomial F u p).eval y) 0

theorem point_mem (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) :
    (polynomial F u p).eval (point F u p x) = 0 := by
  have h := point_zero F u p x (F.pivot u)
  rw [spatial_eq] at h
  simpa only [ProjectionCriticalFamily.spatialEquation, ite_true] using h

noncomputable def samplePoint (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) : Level F u p :=
  ⟨point F u p x, point_mem F u p x⟩

noncomputable def componentMap (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :
    Samples F u p → ConnectedComponents (Level F u p) :=
  fun x => ConnectedComponents.mk (samplePoint F u p x)

theorem componentMap_surjective (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (hv : direction F u (F.pivot u) = 1)
    (hcompact : IsCompact {y | (polynomial F u p).eval y = 0})
    (hregular : ∀ y, (polynomial F u p).eval y = 0 →
      Function.Surjective (fderiv ℝ (fun z => (polynomial F u p).eval z) y))
    (hcritical : ∀ y, (∀ i, (spatial F u p i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (spatial F u p i).eval z) y).IsInvertible) :
    Function.Surjective (componentMap F u p) := by
  intro component
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe component
  obtain ⟨x, hj, _, _⟩ := exists_joined_sample F u p hv hcompact hregular hcritical y.val y.property
  exact ⟨x, ConnectedComponents.coe_eq_coe'.mpr
    (pathComponent_subset_component y hj.joined_subtype)⟩

/-- The actual selected fiber bounds the slice components; candidates over
other parent roots contribute only to the final uniform upper bound. -/
theorem finite_components (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (hv : direction F u (F.pivot u) = 1)
    (hcompact : IsCompact {y | (polynomial F u p).eval y = 0})
    (hregular : ∀ y, (polynomial F u p).eval y = 0 →
      Function.Surjective (fderiv ℝ (fun z => (polynomial F u p).eval z) y))
    (hcritical : ∀ y, (∀ i, (spatial F u p i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (spatial F u p i).eval z) y).IsInvertible) :
    Finite (ConnectedComponents (Level F u p)) ∧
      Nat.card (ConnectedComponents (Level F u p)) ≤ Nat.card (Samples F u p) ∧
      Nat.card (ConnectedComponents (Level F u p)) ≤ BoundedCriticalSampleChildRegularCount.count F u := by
  let : Finite (Samples F u p) := finite_samples F u p
  have hs := componentMap_surjective F u p hv hcompact hregular hcritical
  have hc := Nat.card_le_card_of_surjective _ hs
  exact ⟨Finite.of_surjective _ hs, hc, hc.trans (card_le F u p)⟩

/-- Testing paths between all actual-parent child samples suffices for the
whole compact regular slice, including the empty slice. -/
theorem preconnected_iff_samples (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (hv : direction F u (F.pivot u) = 1)
    (hcompact : IsCompact {y | (polynomial F u p).eval y = 0})
    (hregular : ∀ y, (polynomial F u p).eval y = 0 →
      Function.Surjective (fderiv ℝ (fun z => (polynomial F u p).eval z) y))
    (hcritical : ∀ y, (∀ i, (spatial F u p i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (spatial F u p i).eval z) y).IsInvertible) :
    IsPreconnected {y | (polynomial F u p).eval y = 0} ↔
      ∀ i j : Samples F u p, JoinedIn {y | (polynomial F u p).eval y = 0}
        (point F u p i) (point F u p j) := by
  constructor
  · intro h i j
    let : LocallyPathConnectedSpace (Level F u p) := RegularFiber.locallyPathConnected
      (fun y => (polynomial F u p).eval y) 0
      (fun _ => ((ProjectionCritical.contDiff_eval (RingHom.id ℝ) (polynomial F u p)).of_le le_top).contDiffAt)
      (fun y => hregular y.val y.property)
    let : ConnectedSpace (Level F u p) := isConnected_iff_connectedSpace.mp
      ⟨⟨point F u p i, point_mem F u p i⟩, h⟩
    let : PathConnectedSpace (Level F u p) := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
    exact (joinedIn_iff_joined (point_mem F u p i) (point_mem F u p j)).mpr
      (PathConnectedSpace.joined (samplePoint F u p i) (samplePoint F u p j))
  · intro h
    by_cases hn : Set.Nonempty {y | (polynomial F u p).eval y = 0}
    · apply (isPathConnected_iff.mpr ⟨hn, ?_⟩).isConnected.isPreconnected
      intro y hy z hz
      obtain ⟨i, hi, _, _⟩ := exists_joined_sample F u p hv hcompact hregular hcritical y hy
      obtain ⟨j, hj, _, _⟩ := exists_joined_sample F u p hv hcompact hregular hcritical z hz
      exact (hi.trans (h i j)).trans hj.symm
    · rw [Set.not_nonempty_iff_eq_empty.mp hn]
      exact isPreconnected_empty

end LeanCanny.Connectivity.CriticalSampleChildCoverage
