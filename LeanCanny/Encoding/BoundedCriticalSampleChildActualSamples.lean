/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildParentSelection

/-! # Finite regular child samples over a specified actual parent

The geometric samples are regular joint candidates whose retained coordinate
is the specified parent parameter. Native selection gives their exact short
descriptor language. Accepted words name unique samples, and the native
enumeration of all regular candidates contains every sample in this fiber.
Good directions are still needed to cover all intended critical points.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildActualSamples
open LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter Brackets
open BoundedCriticalSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleChildQueries.roots
  BoundedCriticalRationalCoordinates.parameter BoundedCriticalRationalCoordinates.parameterDegree
  BoundedCriticalSampleLabels.parameter BoundedCriticalSampleHashChoice.descriptor
  BoundedCriticalSampleChildHashChoice.descriptor

def Samples (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :=
  {z : BoundedCriticalSampleChildParameters.Candidates F u //
    z.val.val (BoundedCriticalSampleChildParentThom.first F u) =
      (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val}

theorem finite_samples (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) : Finite (Samples F u p) := by
  let : Finite (BoundedCriticalSampleChildParameters.Candidates F u) :=
    (BoundedCriticalSampleJointGeometry.finite_regular_candidates F.parent F.term F.offset F.dim
      F.directionWidth F.direction u (F.pivot u)).1
  unfold Samples
  infer_instance

theorem card_le (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :
    Nat.card (Samples F u p) ≤ BoundedCriticalSampleChildRegularCount.count F u := by
  let : Finite (BoundedCriticalSampleChildParameters.Candidates F u) :=
    (BoundedCriticalSampleJointGeometry.finite_regular_candidates F.parent F.term F.offset F.dim
      F.directionWidth F.direction u (F.pivot u)).1
  rw [BoundedCriticalSampleChildRegularCount.count_eq_candidates]
  exact Nat.card_le_card_of_injective (fun x : Samples F u p => x.val) Subtype.val_injective

noncomputable def spatial (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :=
  BoundedCriticalSampleJointGeometry.spatial F.parent F.term F.offset F.dim F.directionWidth
    F.direction u (F.pivot u) (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val

noncomputable def point (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) : Fin (F.dim u) → ℝ :=
  fun i => x.val.val.val i.succ

theorem point_cons (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) :
    Fin.cons (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val (point F u p x) = x.val.val.val := by
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  exact x.property.symm

theorem point_injective (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) : Function.Injective (point F u p) := by
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [← point_cons F u p x, ← point_cons F u p y, he]

theorem point_zero (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) :
    ∀ i, (spatial F u p i).eval (point F u p x) = 0 := by
  have H := BoundedCriticalSampleJointGeometry.root_iff F.parent F.term F.offset F.dim F.directionWidth
    F.direction u (F.pivot u) (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val (point F u p x)
  rw [point_cons F u p x] at H
  exact (H.mp x.val.val.property).2

theorem point_regular (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) :
    (fderiv ℝ (fun y => fun i => (spatial F u p i).eval y) (point F u p x)).IsInvertible := by
  have ht := ((BoundedCriticalSampleLabels.mem_rootSet F.parent (pairFst u) _).mp
    (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).property).1
  have H := BoundedCriticalSampleJointGeometry.regular_at_parameter_root F.parent F.term F.offset F.dim F.directionWidth
    F.direction u (F.pivot u) (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val (point F u p x) ht
  rw [point_cons F u p x] at H
  exact H.mp x.val.property

theorem point_complete (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (y : Fin (F.dim u) → ℝ)
    (hy : ∀ i, (spatial F u p i).eval y = 0)
    (hr : (fderiv ℝ (fun z => fun i => (spatial F u p i).eval z) y).IsInvertible) :
    ∃ x : Samples F u p, point F u p x = y := by
  have ht := ((BoundedCriticalSampleLabels.mem_rootSet F.parent (pairFst u) _).mp
    (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).property).1
  have hz := (BoundedCriticalSampleJointGeometry.root_iff F.parent F.term F.offset F.dim F.directionWidth
    F.direction u (F.pivot u) (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val y).mpr ⟨ht, hy⟩
  have hregular := (BoundedCriticalSampleJointGeometry.regular_at_parameter_root F.parent F.term F.offset F.dim F.directionWidth
    F.direction u (F.pivot u) (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val y ht).mpr hr
  exact ⟨⟨⟨⟨Fin.cons (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val y, hz⟩, hregular⟩, rfl⟩, rfl⟩

def SpatialSamples (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :=
  {y : Fin (F.dim u) → ℝ // (∀ i, (spatial F u p i).eval y = 0) ∧
    (fderiv ℝ (fun z => fun i => (spatial F u p i).eval z) y).IsInvertible}

noncomputable def spatialSample (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) : SpatialSamples F u p :=
  ⟨point F u p x, point_zero F u p x, point_regular F u p x⟩

noncomputable def spatialEquiv (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) : Samples F u p ≃ SpatialSamples F u p :=
  Equiv.ofBijective (spatialSample F u p) ⟨fun _ _ he =>
    point_injective F u p (congrArg Subtype.val he), fun y => by
      obtain ⟨x, hx⟩ := point_complete F u p y.val y.property.1 y.property.2
      exact ⟨x, Subtype.ext hx⟩⟩

noncomputable def word (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) : List Bool :=
  BoundedCriticalSampleChildDescriptors.candidateWord F u x.val

theorem word_injective (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) : Function.Injective (word F u p) := by
  intro x y he
  apply Subtype.ext
  apply (BoundedCriticalSampleChildHashEnumeration.rootCandidateEquiv F u).symm.injective
  exact BoundedCriticalSampleChildHashChoice.descriptor_injective F u he

theorem word_length (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) :
    (word F u p x).length ≤ BoundedCriticalSampleChildHashChoice.descriptorWidth F u :=
  BoundedCriticalSampleChildHashChoice.descriptor_length_le F u
    ((BoundedCriticalSampleChildHashEnumeration.rootCandidateEquiv F u).symm x.val)

theorem language_iff (F : Inputs) (u w : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :
    pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p) w) ∈
      BoundedCriticalSampleChildParentSelection.language F ↔ ∃ x : Samples F u p, word F u p x = w := by
  constructor
  · intro hq
    have hv : pair u w ∈ BoundedCriticalSampleChildDescriptors.language F := by
      simpa only [BoundedCriticalSampleChildParentSelection.childLabel,
        BoundedCriticalSampleChildParentSelection.source, BoundedCriticalSampleChildParentSelection.childWord,
        pairFst_pair, pairSnd_pair] using hq.2.1
    have hv' := (BoundedCriticalSampleChildDescriptors.language_iff_candidate F (pair u w)).mp hv
    rw [pairFst_pair, pairSnd_pair] at hv'
    obtain ⟨z, hz⟩ := hv'
    have hs : z.val.val (BoundedCriticalSampleChildParentThom.first F u) =
        (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val := by
      apply (BoundedCriticalSampleChildParentSelection.candidate_packet F u p z).mp
      rw [hz]
      exact hq
    exact ⟨⟨z, hs⟩, hz⟩
  · rintro ⟨x, rfl⟩
    exact (BoundedCriticalSampleChildParentSelection.candidate_packet F u p x.val).mpr x.property

theorem unique_sample (F : Inputs) (u w : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (hq : pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p) w) ∈
      BoundedCriticalSampleChildParentSelection.language F) : ∃! x : Samples F u p, word F u p x = w := by
  obtain ⟨x, hx⟩ := (language_iff F u w p).mp hq
  exact ⟨x, hx, fun y hy => word_injective F u p (hy.trans hx.symm)⟩

theorem word_valid (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) :
    pair u (pair (BoundedCriticalSampleHashChoice.descriptor F.parent (pairFst u) p) (word F u p x)) ∈
      BoundedCriticalSampleChildParentSelection.language F :=
  (language_iff F u (word F u p x) p).mpr ⟨x, rfl⟩

theorem enumerated (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (x : Samples F u p) :
    ∃ r : Fin (BoundedCriticalSampleChildRegularCount.count F u), word F u p x =
      SignStatisticBits.integerCode (BoundedCriticalSampleChildHashEnumeration.value F (pair u (BinaryNatCode.encode r.val))) := by
  obtain ⟨r, hr⟩ := (BoundedCriticalSampleChildHashEnumeration.candidateEquiv F u).surjective x.val
  refine ⟨r, ?_⟩
  rw [word, ← hr]
  exact BoundedCriticalSampleChildDescriptors.candidateWord_enumerated F u r

end LeanCanny.Encoding.BoundedCriticalSampleChildActualSamples
