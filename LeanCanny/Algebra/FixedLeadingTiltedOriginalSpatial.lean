/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.FixedLeadingTiltedSourceFP
public import LeanCanny.Algebra.IntegralMixedOriginalSpatialLeaves

/-! # The actual tilted source supplies both original critical coefficient leaves

The uniform division-free polynomial writer is connected to the charged
coefficient algorithm. The source identity names the literal spatial source;
no coefficient evaluator for that source is supplied as a premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedLeadingTiltedOriginalSpatial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open LeanCanny.ETR

def word (t : List Bool → Term) (k u : List Bool → ℕ) (r : List Bool) : List Bool :=
  FixedLeadingTiltedSourceFP.lowWord (k r)
    (FixedLeadingTiltedSourceFP.originalDegree t r) (u r) (t r)

theorem word_FP (t : List Bool → Term) (k u : List Bool → ℕ)
    (ht : (fun r => (t r).toData.toBits) ∈ FP) (hk : UnaryFn k) (hu : UnaryFn u) :
    word t k u ∈ FP :=
  FixedLeadingTiltedSourceFP.original_lowWord_FP ht hk hu

theorem word_scope (P : Parameters) (t : List Bool → Term) (k : List Bool → ℕ)
    (u : (r : List Bool) → Fin (P.ambient r))
    (ha : ∀ r, (t r).arity ≤ P.ambient r) (r : List Bool) :
    (TermView.term (word t k (fun r => (u r).val) r)).arity ≤ P.ambient r + 1 :=
  FixedLeadingTiltedSourceFP.lowWord_arity (k r) _ (u r) (t r) (ha r)

theorem word_polynomial (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (t : List Bool → Term) (k : List Bool → ℕ)
    (u : (r : List Bool) → Fin (P.ambient r))
    (hs : ∀ r, D.spatial r = FixedLeadingTiltedSource.source (k r)
      (FixedLeadingTiltedSourceFP.originalDegree t r) (u r) (t r) (t r).degreeBound_le_dataSize)
    (r : List Bool) :
    (TermView.term (word t k (fun r => (u r).val) r)).finitePolynomial (P.ambient r + 1) =
      (D.spatial r).low := by
  exact (FixedLeadingTiltedSourceFP.lowWord_polynomial (k r) _ (u r) (t r)
    (t r).degreeBound_le_dataSize).trans (congrArg (fun s => s.low) (hs r)).symm

theorem controls (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (full : IntegralMixedFullHistoryFamilyBits.Metadata P D)
    (physical : IntegralMixedPhysicalQueryBits.InputMetadata
      (IntegralMixedFullCriticalDispatcherBits.physicalFamily P D))
    (t : List Bool → Term) (k : List Bool → ℕ)
    (u : (r : List Bool) → Fin (P.ambient r))
    (ht : (fun r => (t r).toData.toBits) ∈ FP) (hk : UnaryFn k)
    (hu : UnaryFn (fun r => (u r).val)) (ha : ∀ r, (t r).arity ≤ P.ambient r)
    (hs : ∀ r, D.spatial r = FixedLeadingTiltedSource.source (k r)
      (FixedLeadingTiltedSourceFP.originalDegree t r) (u r) (t r) (t r).degreeBound_le_dataSize) :
    IntegralMixedFullCriticalDispatcherBits.Controls P D :=
  IntegralMixedOriginalSpatialTermBits.controls P a D full physical
    (word t k (fun r => (u r).val)) (word_FP t k _ ht hk hu)
    (word_scope P t k u ha) (word_polynomial P D t k u hs)

end LeanCanny.Algebra.FixedLeadingTiltedOriginalSpatial
