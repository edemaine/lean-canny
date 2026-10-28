/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildActualSamples
public import LeanCanny.Geometry.ComponentCriticalSampling
public import LeanCanny.Geometry.ProjectionCriticalSourceRegularity
public import LeanCanny.Encoding.BoundedFullSampleBlockGeometry

/-! # Regular child descriptors sample every component of a contained shared-source block

A normalized direction whose spatial critical points are all regular makes
the constructed finite actual-parent samples meet every component of the
compact regular slice. Every point can reach a sample with an accepted short
native descriptor. Compactness follows from the source construction. Accepted
native directions supply critical regularity; normalization leaves the rows unchanged.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FullSampleChildCoverage
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding LeanCanny.Geometry
open BoundedFullSampleChildSource (Inputs)
open BoundedFullSampleChildActualSamples
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleBlockScaling.original
  BoundedCriticalSampleLabels.parameter

noncomputable def polynomial (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) :=
  BoundedFullSampleBlockScaling.original F.block u p

noncomputable def direction (F : Inputs) (u : List Bool) (i : Fin (F.block.dim u)) : ℝ :=
  if i = F.pivot u then 1 else
    BoundedFullSampleBlockCriticalSource.direction F.block.dim F.directionWidth F.direction u i

theorem direction_pivot (F : Inputs) (u : List Bool) : direction F u (F.pivot u) = 1 := by
  simp only [direction, ite_true]

theorem spatial_eq (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) :
    spatial F u p = ProjectionCriticalFamily.spatialEquation (polynomial F u p) (F.pivot u) (direction F u) := by
  funext i
  by_cases hi : i = F.pivot u <;>
    simp only [spatial, BoundedFullSampleChildParameters.originalRows, polynomial,
      ProjectionCriticalFamily.spatialEquation, direction, hi, ite_true, ite_false]

theorem compact_level (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (hfit : F.block.offset u + F.block.dim u ≤ F.block.source.dim u + 4) (t : ℝ) :
    IsCompact {y | (polynomial F u p).eval y = t} :=
  BoundedFullSampleBlockGeometry.compact_level F.block u p hfit t

theorem hypersurface_regular (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (hcritical : ∀ y, (∀ i, (spatial F u p i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (spatial F u p i).eval z) y).IsInvertible) :
    ∀ y, (polynomial F u p).eval y = 0 →
      Function.Surjective (fderiv ℝ (fun z => (polynomial F u p).eval z) y) := by
  rw [spatial_eq] at hcritical
  exact ProjectionCriticalSourceRegularity.source_regular (polynomial F u p) (F.pivot u) (direction F u) hcritical

theorem exists_joined_sample (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (hfit : F.block.offset u + F.block.dim u ≤ F.block.source.dim u + 4)
    (hcritical : ∀ y, (∀ i, (spatial F u p i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (spatial F u p i).eval z) y).IsInvertible)
    (y : Fin (F.block.dim u) → ℝ) (hy : (polynomial F u p).eval y = 0) :
    ∃ x : Samples F u p,
      JoinedIn {z | (polynomial F u p).eval z = 0} y (point F u p x) ∧
      (word F u p x).length ≤ BoundedFullSampleChildHashChoice.descriptorWidth F u ∧
      pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.block.parent (pairFst u) p) (word F u p x)) ∈
        BoundedFullSampleChildParentSelection.language F := by
  obtain ⟨z, hj, hz⟩ := ComponentCriticalSampling.exists_joined_critical
    (polynomial F u p) (F.pivot u) (direction F u) (direction_pivot F u) 0 (compact_level F u p hfit 0)
      (hypersurface_regular F u p hcritical) y hy
  have hzero : ∀ i, (spatial F u p i).eval z = 0 := by
    rw [spatial_eq]
    apply (ProjectionCriticalFamily.spatial_zero_iff (RingHom.id ℝ) (polynomial F u p)
      (F.pivot u) (direction F u) (direction_pivot F u) z).mpr
    exact (ProjectionCriticalBranches.value_iff (polynomial F u p) (F.pivot u) (direction F u) (direction_pivot F u) 0 z).mp hz
  obtain ⟨x, hx⟩ := point_complete F u p z hzero (hcritical z hzero)
  refine ⟨x, ?_, word_length F u p x, word_valid F u p x⟩
  simpa only [hx] using hj

abbrev Level (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) :=
  RegularFiber.Fiber (fun y => (polynomial F u p).eval y) 0

theorem point_mem (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) (x : Samples F u p) :
    (polynomial F u p).eval (point F u p x) = 0 := by
  have h := point_zero F u p x (F.pivot u)
  rw [spatial_eq] at h
  simpa only [ProjectionCriticalFamily.spatialEquation, ite_true] using h

noncomputable def samplePoint (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) (x : Samples F u p) : Level F u p :=
  ⟨point F u p x, point_mem F u p x⟩

noncomputable def componentMap (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) :
    Samples F u p → ConnectedComponents (Level F u p) :=
  fun x => ConnectedComponents.mk (samplePoint F u p x)

theorem componentMap_surjective (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (hfit : F.block.offset u + F.block.dim u ≤ F.block.source.dim u + 4)
    (hcritical : ∀ y, (∀ i, (spatial F u p i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (spatial F u p i).eval z) y).IsInvertible) :
    Function.Surjective (componentMap F u p) := by
  intro component
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe component
  obtain ⟨x, hj, _, _⟩ := exists_joined_sample F u p hfit hcritical y.val y.property
  exact ⟨x, ConnectedComponents.coe_eq_coe'.mpr
    (pathComponent_subset_component y hj.joined_subtype)⟩

/-- The actual selected fiber bounds the slice components; candidates over
other parent roots contribute only to the final uniform upper bound. -/
theorem finite_components (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (hfit : F.block.offset u + F.block.dim u ≤ F.block.source.dim u + 4)
    (hcritical : ∀ y, (∀ i, (spatial F u p i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (spatial F u p i).eval z) y).IsInvertible) :
    Finite (ConnectedComponents (Level F u p)) ∧
      Nat.card (ConnectedComponents (Level F u p)) ≤ Nat.card (Samples F u p) ∧
      Nat.card (ConnectedComponents (Level F u p)) ≤ BoundedFullSampleChildRegularCount.count F u := by
  let : Finite (Samples F u p) := finite_samples F u p
  have hs := componentMap_surjective F u p hfit hcritical
  have hc := Nat.card_le_card_of_surjective _ hs
  exact ⟨Finite.of_surjective _ hs, hc, hc.trans (card_le F u p)⟩

/-- Testing paths between all actual-parent child samples suffices for the
whole compact regular slice, including the empty slice. -/
theorem preconnected_iff_samples (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (hfit : F.block.offset u + F.block.dim u ≤ F.block.source.dim u + 4)
    (hcritical : ∀ y, (∀ i, (spatial F u p i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (spatial F u p i).eval z) y).IsInvertible) :
    IsPreconnected {y | (polynomial F u p).eval y = 0} ↔
      ∀ i j : Samples F u p, JoinedIn {y | (polynomial F u p).eval y = 0}
        (point F u p i) (point F u p j) := by
  have hregular := hypersurface_regular F u p hcritical
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
      obtain ⟨i, hi, _, _⟩ := exists_joined_sample F u p hfit hcritical y hy
      obtain ⟨j, hj, _, _⟩ := exists_joined_sample F u p hfit hcritical z hz
      exact (hi.trans (h i j)).trans hj.symm
    · rw [Set.not_nonempty_iff_eq_empty.mp hn]
      exact isPreconnected_empty

theorem selected_critical_regular (F : BoundedFullBlockDirectionChoice.Inputs) (u : List Bool)
    (hg : BoundedFullBlockDirectionChoice.Good F (pairFst u) (BoundedFullBlockDirectionChoice.record F (pairFst u)))
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :
    ∀ y, (∀ i, (spatial (BoundedFullSampleSelectedDirection.child F) u p i).eval y = 0) →
      (fderiv ℝ (fun z => fun i => (spatial (BoundedFullSampleSelectedDirection.child F) u p i).eval z) y).IsInvertible :=
  BoundedFullSampleSelectedDirection.critical_regular F u hg p

theorem selected_exists_joined_sample (F : BoundedFullBlockDirectionChoice.Inputs) (u : List Bool)
    (hg : BoundedFullBlockDirectionChoice.Good F (pairFst u) (BoundedFullBlockDirectionChoice.record F (pairFst u)))
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (hfit : F.offset (pairFst u) + (F.free (pairFst u) + 1) ≤ F.source.dim (pairFst u) + 4)
    (y : Fin (F.free (pairFst u) + 1) → ℝ)
    (hy : (polynomial (BoundedFullSampleSelectedDirection.child F) u p).eval y = 0) :
    ∃ x : Samples (BoundedFullSampleSelectedDirection.child F) u p,
      JoinedIn {z | (polynomial (BoundedFullSampleSelectedDirection.child F) u p).eval z = 0}
        y (point (BoundedFullSampleSelectedDirection.child F) u p x) ∧
      (word (BoundedFullSampleSelectedDirection.child F) u p x).length ≤
        BoundedFullSampleChildHashChoice.descriptorWidth (BoundedFullSampleSelectedDirection.child F) u ∧
      pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p)
        (word (BoundedFullSampleSelectedDirection.child F) u p x)) ∈
          BoundedFullSampleChildParentSelection.language (BoundedFullSampleSelectedDirection.child F) :=
  exists_joined_sample (BoundedFullSampleSelectedDirection.child F) u p hfit
    (selected_critical_regular F u hg p) y hy

theorem selected_finite_components (F : BoundedFullBlockDirectionChoice.Inputs) (u : List Bool)
    (hg : BoundedFullBlockDirectionChoice.Good F (pairFst u) (BoundedFullBlockDirectionChoice.record F (pairFst u)))
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (hfit : F.offset (pairFst u) + (F.free (pairFst u) + 1) ≤ F.source.dim (pairFst u) + 4) :
    Finite (ConnectedComponents (Level (BoundedFullSampleSelectedDirection.child F) u p)) ∧
      Nat.card (ConnectedComponents (Level (BoundedFullSampleSelectedDirection.child F) u p)) ≤
        Nat.card (Samples (BoundedFullSampleSelectedDirection.child F) u p) ∧
      Nat.card (ConnectedComponents (Level (BoundedFullSampleSelectedDirection.child F) u p)) ≤
        BoundedFullSampleChildRegularCount.count (BoundedFullSampleSelectedDirection.child F) u :=
  finite_components (BoundedFullSampleSelectedDirection.child F) u p hfit (selected_critical_regular F u hg p)

/-- The unfrozen block is exactly the constructed source polynomial. -/
theorem whole_polynomial (P S : BoundedFullWriter.Readers) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples P (pairFst u)) :
    polynomial (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p =
      BoundedFullCriticalSamples.realPolynomial S (pairFst u) := by
  unfold polynomial
  rw [BoundedFullSampleSelectedDirection.original_eq]
  exact CoordinateBlockSpecialization.finite_all _ _ _

/-- The initial whole source supplies every geometric sampling premise. -/
theorem whole_exists_joined_sample (P S : BoundedFullWriter.Readers) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples P (pairFst u)) (y : Fin (S.dim (pairFst u) + 4) → ℝ)
    (hy : (polynomial (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p).eval y = 0) :
    ∃ x : Samples (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p,
      JoinedIn {z | (polynomial (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p).eval z = 0}
        y (point (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p x) ∧
      (word (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p x).length ≤
        BoundedFullSampleChildHashChoice.descriptorWidth (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u ∧
      pair u (pair (BoundedCriticalSampleHashChoice.descriptor P (pairFst u) p)
        (word (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p x)) ∈
          BoundedFullSampleChildParentSelection.language
            (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) := by
  apply selected_exists_joined_sample (BoundedFullBlockDirectionChoice.whole P S) u
    (BoundedFullBlockDirectionChoice.whole_record_good P S (pairFst u)) p ?_ y hy
  change 0 + (S.dim (pairFst u) + 3 + 1) ≤ S.dim (pairFst u) + 4
  omega

end LeanCanny.Connectivity.FullSampleChildCoverage
