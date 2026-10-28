/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildParentSelection
public import LeanCanny.Encoding.BoundedFullSampleSelectedDirection

/-! # Finite regular child samples over a specified actual parent

The geometric samples are regular original-block critical points encoded by
joint candidates whose retained coordinate
is the specified parent parameter. Native selection gives their exact short
descriptor language. Accepted words name unique samples, and the native
enumeration of all regular candidates contains every sample in this fiber.
Good directions are still needed to cover all intended critical points.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildActualSamples
open LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter Brackets
open BoundedFullSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildQueries.roots
  BoundedCriticalRationalCoordinates.parameter BoundedCriticalRationalCoordinates.parameterDegree
  BoundedCriticalSampleLabels.parameter BoundedCriticalSampleHashChoice.descriptor
  BoundedFullSampleChildHashChoice.descriptor

def Samples (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) :=
  {z : BoundedFullSampleChildParameters.Candidates F u //
    z.val.val (BoundedFullSampleChildParentThom.first F u) =
      (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) p).val}

theorem finite_samples (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) : Finite (Samples F u p) := by
  let : Finite (BoundedFullSampleChildParameters.Candidates F u) :=
    (BoundedFullSampleJointGeometry.finite_regular_candidates F.block
      F.directionWidth F.direction u (F.pivot u)).1
  unfold Samples
  infer_instance

theorem card_le (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) :
    Nat.card (Samples F u p) ≤ BoundedFullSampleChildRegularCount.count F u := by
  let : Finite (BoundedFullSampleChildParameters.Candidates F u) :=
    (BoundedFullSampleJointGeometry.finite_regular_candidates F.block
      F.directionWidth F.direction u (F.pivot u)).1
  rw [BoundedFullSampleChildRegularCount.count_eq_candidates]
  exact Nat.card_le_card_of_injective (fun x : Samples F u p => x.val) Subtype.val_injective

noncomputable def spatial (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) :=
  BoundedFullSampleChildParameters.originalRows F u p

noncomputable def point (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) (x : Samples F u p) : Fin (F.block.dim u) → ℝ :=
  fun i => x.val.val.val i.succ

theorem point_cons (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) (x : Samples F u p) :
    Fin.cons (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) p).val (point F u p x) = x.val.val.val := by
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  exact x.property.symm

theorem point_injective (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) : Function.Injective (point F u p) := by
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [← point_cons F u p x, ← point_cons F u p y, he]

theorem point_zero (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) (x : Samples F u p) :
    ∀ i, (spatial F u p i).eval (point F u p x) = 0 := by
  have H := BoundedFullSampleJointGeometry.sample_root_iff F.block F.directionWidth
    F.direction u p (F.pivot u) (point F u p x)
  rw [point_cons F u p x] at H
  exact H.mp x.val.val.property

theorem point_regular (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) (x : Samples F u p) :
    (fderiv ℝ (fun y => fun i => (spatial F u p i).eval y) (point F u p x)).IsInvertible := by
  have H := BoundedFullSampleJointGeometry.sample_regular_iff F.block F.directionWidth
    F.direction u p (F.pivot u) (point F u p x)
  rw [point_cons F u p x] at H
  exact H.mp x.val.property

theorem point_complete (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) (y : Fin (F.block.dim u) → ℝ)
    (hy : ∀ i, (spatial F u p i).eval y = 0)
    (hr : (fderiv ℝ (fun z => fun i => (spatial F u p i).eval z) y).IsInvertible) :
    ∃ x : Samples F u p, point F u p x = y := by
  have hz := (BoundedFullSampleJointGeometry.sample_root_iff F.block F.directionWidth
    F.direction u p (F.pivot u) y).mpr hy
  have hregular := (BoundedFullSampleJointGeometry.sample_regular_iff F.block F.directionWidth
    F.direction u p (F.pivot u) y).mpr hr
  exact ⟨⟨⟨⟨Fin.cons (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) p).val y, hz⟩, hregular⟩, rfl⟩, rfl⟩

def SpatialSamples (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) :=
  {y : Fin (F.block.dim u) → ℝ // (∀ i, (spatial F u p i).eval y = 0) ∧
    (fderiv ℝ (fun z => fun i => (spatial F u p i).eval z) y).IsInvertible}

noncomputable def spatialSample (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) (x : Samples F u p) : SpatialSamples F u p :=
  ⟨point F u p x, point_zero F u p x, point_regular F u p x⟩

noncomputable def spatialEquiv (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) : Samples F u p ≃ SpatialSamples F u p :=
  Equiv.ofBijective (spatialSample F u p) ⟨fun _ _ he =>
    point_injective F u p (congrArg Subtype.val he), fun y => by
      obtain ⟨x, hx⟩ := point_complete F u p y.val y.property.1 y.property.2
      exact ⟨x, Subtype.ext hx⟩⟩

noncomputable def word (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) (x : Samples F u p) : List Bool :=
  BoundedFullSampleChildDescriptors.candidateWord F u x.val

theorem word_injective (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) : Function.Injective (word F u p) := by
  intro x y he
  apply Subtype.ext
  apply (BoundedFullSampleChildHashEnumeration.rootCandidateEquiv F u).symm.injective
  exact BoundedFullSampleChildHashChoice.descriptor_injective F u he

theorem word_length (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) (x : Samples F u p) :
    (word F u p x).length ≤ BoundedFullSampleChildHashChoice.descriptorWidth F u :=
  BoundedFullSampleChildHashChoice.descriptor_length_le F u
    ((BoundedFullSampleChildHashEnumeration.rootCandidateEquiv F u).symm x.val)

theorem language_iff (F : Inputs) (u w : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) :
    pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.block.parent (pairFst u) p) w) ∈
      BoundedFullSampleChildParentSelection.language F ↔ ∃ x : Samples F u p, word F u p x = w := by
  constructor
  · intro hq
    have hv : pair u w ∈ BoundedFullSampleChildDescriptors.language F := by
      simpa only [BoundedFullSampleChildParentSelection.childLabel,
        BoundedFullSampleChildParentSelection.source, BoundedFullSampleChildParentSelection.childWord,
        pairFst_pair, pairSnd_pair] using hq.2.1
    have hv' := (BoundedFullSampleChildDescriptors.language_iff_candidate F (pair u w)).mp hv
    rw [pairFst_pair, pairSnd_pair] at hv'
    obtain ⟨z, hz⟩ := hv'
    have hs : z.val.val (BoundedFullSampleChildParentThom.first F u) =
        (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) p).val := by
      apply (BoundedFullSampleChildParentSelection.candidate_packet F u p z).mp
      rw [hz]
      exact hq
    exact ⟨⟨z, hs⟩, hz⟩
  · rintro ⟨x, rfl⟩
    exact (BoundedFullSampleChildParentSelection.candidate_packet F u p x.val).mpr x.property

theorem unique_sample (F : Inputs) (u w : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u))
    (hq : pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.block.parent (pairFst u) p) w) ∈
      BoundedFullSampleChildParentSelection.language F) : ∃! x : Samples F u p, word F u p x = w := by
  obtain ⟨x, hx⟩ := (language_iff F u w p).mp hq
  exact ⟨x, hx, fun y hy => word_injective F u p (hy.trans hx.symm)⟩

theorem word_valid (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) (x : Samples F u p) :
    pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.block.parent (pairFst u) p) (word F u p x)) ∈
      BoundedFullSampleChildParentSelection.language F :=
  (language_iff F u (word F u p x) p).mpr ⟨x, rfl⟩

theorem enumerated (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) (x : Samples F u p) :
    ∃ r : Fin (BoundedFullSampleChildRegularCount.count F u), word F u p x =
      SignStatisticBits.integerCode (BoundedFullSampleChildHashEnumeration.value F (pair u (BinaryNatCode.encode r.val))) := by
  obtain ⟨r, hr⟩ := (BoundedFullSampleChildHashEnumeration.candidateEquiv F u).surjective x.val
  refine ⟨r, ?_⟩
  rw [word, ← hr]
  exact BoundedFullSampleChildDescriptors.candidateWord_enumerated F u r

/-- Accepted directions give actual-parent labels for every original block
critical point, with no separate pointwise regularity witness. -/
theorem selected_point_complete (F : BoundedFullBlockDirectionChoice.Inputs) (u : List Bool)
    (hg : BoundedFullBlockDirectionChoice.Good F (pairFst u) (BoundedFullBlockDirectionChoice.record F (pairFst u)))
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (y : Fin (F.free (pairFst u) + 1) → ℝ)
    (hy : ∀ i, (spatial (BoundedFullSampleSelectedDirection.child F) u p i).eval y = 0) :
    ∃ x : Samples (BoundedFullSampleSelectedDirection.child F) u p,
      point (BoundedFullSampleSelectedDirection.child F) u p x = y ∧
      (word (BoundedFullSampleSelectedDirection.child F) u p x).length ≤
        BoundedFullSampleChildHashChoice.descriptorWidth (BoundedFullSampleSelectedDirection.child F) u ∧
      pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p)
        (word (BoundedFullSampleSelectedDirection.child F) u p x)) ∈
          BoundedFullSampleChildParentSelection.language (BoundedFullSampleSelectedDirection.child F) := by
  obtain ⟨x, hx⟩ := point_complete (BoundedFullSampleSelectedDirection.child F) u p y hy
    (BoundedFullSampleSelectedDirection.critical_regular F u hg p y hy)
  exact ⟨x, hx, word_length _ _ _ x, word_valid _ _ _ x⟩

theorem whole_point_complete (P S : Readers) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples P (pairFst u)) (y : Fin (S.dim (pairFst u) + 4) → ℝ)
    (hy : ∀ i, (spatial (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p i).eval y = 0) :
    ∃ x : Samples (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p,
      point (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p x = y ∧
      (word (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p x).length ≤
        BoundedFullSampleChildHashChoice.descriptorWidth (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u ∧
      pair u (pair (BoundedCriticalSampleHashChoice.descriptor P (pairFst u) p)
        (word (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p x)) ∈
          BoundedFullSampleChildParentSelection.language
            (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) :=
  selected_point_complete (BoundedFullBlockDirectionChoice.whole P S) u
    (BoundedFullBlockDirectionChoice.whole_record_good P S (pairFst u)) p y hy

end LeanCanny.Encoding.BoundedFullSampleChildActualSamples
