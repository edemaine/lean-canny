/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildDescriptors
public import LeanCanny.Encoding.BoundedFullSampleSelectedDirection

/-! # Canonical child descriptors for original block critical points

Accepted words name unique regular joint tuples. Every regular critical point
over an actual parent has one such word, with the derived native length
allowance. Accepted selected directions supply the regularity premise. The
initial whole source supplies selection success without a separate witness.
Descriptor-level validation of the specified parent remains a later step.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildDescriptorGeometry
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open BoundedFullSampleChildSource (Inputs count)
open BoundedFullSampleChildParameters (Candidates originalRows)
open BoundedFullSampleChildDescriptors (candidateWord language)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] candidateWord originalRows
  BoundedFullSampleBlockScaling.original pair pairFst pairSnd

def Names (F : Inputs) (u w : List Bool) (x : Fin (count F u) → ℝ) : Prop :=
  ∃ z : Candidates F u, z.val.val = x ∧ candidateWord F u z = w

theorem names_valid (F : Inputs) (u w : List Bool) (x : Fin (count F u) → ℝ) (h : Names F u w x) :
    pair u w ∈ language F := by
  obtain ⟨z, _, hz⟩ := h
  apply (BoundedFullSampleChildDescriptors.language_iff_candidate F (pair u w)).mpr
  rw [pairFst_pair, pairSnd_pair]
  exact ⟨z, hz⟩

theorem names_length (F : Inputs) (u w : List Bool) (x : Fin (count F u) → ℝ) (h : Names F u w x) :
    w.length ≤ BoundedFullSampleChildHashChoice.descriptorWidth F u := by
  simpa only [pairFst_pair, pairSnd_pair] using
    BoundedFullSampleChildDescriptors.length_bound F (pair u w) (names_valid F u w x h)

theorem names_tuple_unique (F : Inputs) (u w : List Bool) (x y : Fin (count F u) → ℝ)
    (hx : Names F u w x) (hy : Names F u w y) : x = y := by
  obtain ⟨z, hz, hwz⟩ := hx
  obtain ⟨z', hz', hwz'⟩ := hy
  unfold candidateWord at hwz hwz'
  have he : z = z' := by
    apply (BoundedFullSampleChildHashEnumeration.rootCandidateEquiv F u).symm.injective
    exact BoundedFullSampleChildHashChoice.descriptor_injective F u (hwz.trans hwz'.symm)
  exact hz.symm.trans ((congrArg (fun a : Candidates F u => a.val.val) he).trans hz')

theorem sample_descriptor (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.block.parent (pairFst u)) (y : Fin (F.block.dim u) → ℝ)
    (hy : ∀ i, (originalRows F u p i).eval y = 0)
    (hr : (fderiv ℝ (fun z => fun i => (originalRows F u p i).eval z) y).IsInvertible) :
    ∃! w : List Bool,
      Names F u w (Fin.cons (BoundedCriticalSampleLabels.parameter F.block.parent (pairFst u) p).val y) := by
  unfold originalRows at hy hr
  obtain ⟨z, hz⟩ := BoundedFullSampleJointGeometry.regular_candidate_at_sample
    F.block F.directionWidth F.direction u p (F.pivot u) y hy hr
  refine ⟨candidateWord F u z, ⟨z, hz, rfl⟩, ?_⟩
  rintro w ⟨z', hz', hw⟩
  have he : z' = z := by
    apply Subtype.ext
    apply Subtype.ext
    exact hz'.trans hz.symm
  rw [← hw, he]

theorem selected_descriptor (F : BoundedFullBlockDirectionChoice.Inputs) (u : List Bool)
    (hg : BoundedFullBlockDirectionChoice.Good F (pairFst u) (BoundedFullBlockDirectionChoice.record F (pairFst u)))
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) (y : Fin (F.free (pairFst u) + 1) → ℝ)
    (hy : ∀ i, (originalRows (BoundedFullSampleSelectedDirection.child F) u p i).eval y = 0) :
    ∃! w : List Bool, Names (BoundedFullSampleSelectedDirection.child F) u w
      (Fin.cons (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val y) :=
  sample_descriptor (BoundedFullSampleSelectedDirection.child F) u p y hy
    (BoundedFullSampleSelectedDirection.critical_regular F u hg p y hy)

theorem whole_descriptor (P S : BoundedFullWriter.Readers) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples P (pairFst u)) (y : Fin (S.dim (pairFst u) + 4) → ℝ)
    (hy : ∀ i, (originalRows (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u p i).eval y = 0) :
    ∃! w : List Bool, Names (BoundedFullSampleSelectedDirection.child (BoundedFullBlockDirectionChoice.whole P S)) u w
      (Fin.cons (BoundedCriticalSampleLabels.parameter P (pairFst u) p).val y) :=
  selected_descriptor (BoundedFullBlockDirectionChoice.whole P S) u
    (BoundedFullBlockDirectionChoice.whole_record_good P S (pairFst u)) p y hy

end LeanCanny.Encoding.BoundedFullSampleChildDescriptorGeometry
