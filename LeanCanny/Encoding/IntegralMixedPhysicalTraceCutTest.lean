/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedTest
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedTraceCuts

/-! # Original-only cut coefficient tests on the same marked full vertex -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalTraceCutTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

theorem key_context (c : List Bool) :
    (bank hn ht ha hR outer).key c=(bank hn ht ha hR outer).key (pair (pairFst c) []) :=by
  cases outer
  · change IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n c=
      IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (pair (pairFst c) [])
    simp only [IntegralMixedAuxiliaryMarkedRecordPlan.bankKey,pairFst_pair]
  · change IntegralMixedAuxiliaryOuterRecordPlan.bankKey n c=
      IntegralMixedAuxiliaryOuterRecordPlan.bankKey n (pair (pairFst c) [])
    simp only [IntegralMixedAuxiliaryOuterRecordPlan.bankKey,pairFst_pair]

theorem factor_positive : ∀root,1≤(bank hn ht ha hR outer).factor root :=by
  cases outer
  · exact IntegralMixedAuxiliaryMarkedRecordPlan.factor_positive hn ht ha
  · exact IntegralMixedAuxiliaryOuterRecordPlan.factor_positive hn ht ha

theorem fallback : ∀q,IntegralMixedFramedOriginalBounds.FallbackBounds
    (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
    (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).seed q :=by
  cases outer
  · exact (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedBounds hn ht ha hR).fallback
  · exact (IntegralMixedAuxiliaryOuterRecordPlan.certifiedBounds hn ht ha hR).fallback

noncomputable def probeControls : IntegralMixedFramedCurrentQNativeBits.Controls
    (IntegralMixedFramedCutProbeTaskBits.parameters (bank hn ht ha hR outer).parameters
      (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed)
    (IntegralMixedFramedCutProbeTransportBits.plan (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
      (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed)
    (IntegralMixedFramedCutProbeTransportBits.data (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
      (bank hn ht ha hR outer).data (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed) :=by
  cases outer
  · exact IntegralMixedAuxiliaryMarkedTraceCuts.probeControls hn ht ha hR
  · exact IntegralMixedFramedPlannedProbe.controls
      (IntegralMixedAuxiliaryOuterRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryOuterRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryOuterRecordPlan.data hn ht ha R)
      (fun _ : List Bool=>3) (IntegralMixedAuxiliaryOuterRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryOuterRecordPlan.seed hn ht ha hR)
      (IntegralMixedAuxiliaryOuterRecordPlan.callerControls hn ht ha hR)

theorem probeBounds : IntegralMixedFramedCurrentQNativeBits.Bounds
    (IntegralMixedFramedCutProbeTaskBits.parameters (bank hn ht ha hR outer).parameters
      (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed)
    (IntegralMixedFramedCutProbeTransportBits.plan (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
      (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed)
    (IntegralMixedFramedCutProbeTransportBits.data (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
      (bank hn ht ha hR outer).data (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed)
    (probeControls hn ht ha hR outer) :=by
  cases outer
  · exact IntegralMixedAuxiliaryMarkedTraceCuts.probeBounds hn ht ha hR
  · exact IntegralMixedFramedPlannedProbe.bounds
      (IntegralMixedAuxiliaryOuterRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryOuterRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryOuterRecordPlan.data hn ht ha R)
      (fun _ : List Bool=>3) (IntegralMixedAuxiliaryOuterRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryOuterRecordPlan.seed hn ht ha hR)
      (IntegralMixedAuxiliaryOuterRecordPlan.callerControls hn ht ha hR)
      (IntegralMixedAuxiliaryOuterRecordPlan.callerBounds hn ht ha hR)

noncomputable def source :=IntegralFramedPhysicalTraceCutSource.source
  (bank hn ht ha hR outer) (key_context hn ht ha hR outer)
  (factor_positive hn ht ha hR outer) (fallback hn ht ha hR outer)

noncomputable def value :=IntegralFramedPhysicalSuffixTest.value (bank hn ht ha hR outer)
  (tables hn ht ha hR outer) (represents hn ht ha hR outer) (source hn ht ha hR outer)

attribute [local irreducible] bank tables source value probeControls

theorem source_access : (source hn ht ha hR outer).Access :=by
  unfold source
  exact IntegralFramedPhysicalTraceCutSource.source_access
    (bank hn ht ha hR outer) (key_context hn ht ha hR outer)
    (factor_positive hn ht ha hR outer) (fallback hn ht ha hR outer)
    (native hn ht ha hR outer) (probeControls hn ht ha hR outer) (probeBounds hn ht ha hR outer)

theorem evaluator (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer))) :
    SpaceFunction (value hn ht ha hR outer) :=by
  unfold value source
  exact IntegralFramedPhysicalTraceCutSource.evaluator
    (bank hn ht ha hR outer) (key_context hn ht ha hR outer)
    (factor_positive hn ht ha hR outer) (fallback hn ht ha hR outer)
    (native hn ht ha hR outer) (probeControls hn ht ha hR outer) (probeBounds hn ht ha hR outer)
    (tables hn ht ha hR outer) (represents hn ht ha hR outer) (tables_native hn ht ha hR outer) ER

theorem packet (c w d : List Bool) (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) c w) :
    value hn ht ha hR outer (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign (((source hn ht ha hR outer).polynomial c d).eval₂ (Int.castRingHom ℝ)
        (fun i=>(SquareSampleCompleteVertices.candidate (input hn ht ha hR outer) c w hv).val
          (IntegralFramedPhysicalSuffixTest.columns (bank hn ht ha hR outer) (tables hn ht ha hR outer)
            (represents hn ht ha hR outer) (source hn ht ha hR outer) c d i)))) :=by
  unfold value
  exact IntegralFramedPhysicalSuffixTest.packet (bank hn ht ha hR outer) (tables hn ht ha hR outer)
    (represents hn ht ha hR outer) (source hn ht ha hR outer) c w d hv

end LeanCanny.Encoding.IntegralMixedPhysicalTraceCutTest
