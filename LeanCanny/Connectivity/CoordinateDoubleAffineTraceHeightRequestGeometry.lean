/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceHeightRequests
public import LeanCanny.Encoding.CoordinateDoubleAffineChildHeightGeometry
public import LeanCanny.Connectivity.CoordinateDoubleAffineTraceChildConnectivity

/-! # Fixed-height recursive requests denote the actual frozen slices

The emitted label decodes to the original fixed-height child, including at
singular slices. The shared-source coordinate cast preserves connectivity.
This supplies geometric semantics for the guarded resumable request, without
assuming a decision procedure for the requested lower-dimensional slice.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CoordinateDoubleAffineTraceHeightRequestGeometry
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open CoordinateDoubleAffineTrace
open scoped Classical

theorem heightFrameWord_preconnected (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (hw : SquareSampleCompleteVertices.Valid
      (CoordinateDoubleAffineTraceHeightRequests.criticalInput P d old level) q w) :
    IsPreconnected (FlatAffineCompleteComponentSamples.slice (inputs P d old level) (append false q)
      (FlatAffineCompleteVertices.vertexEquiv (inputs P d old level) (cone P d old level) (append false q)
        ⟨heightFrameWord P d old level (LeanCanny.pair q w), heightFrameWord_valid P d old level q w hv hw⟩)) ↔
      IsPreconnected (FlatAffineCompleteComponentSamples.slice
        (CoordinateDoubleAffineChildRecords.inputs false (readers P) (depth d) (objective d old) (levels P d old level)) q
        (CoordinateDoubleAffineChildRecords.heightRoot (readers P) (depth d) (objective d old) (levels P d old level) q
          (FlatAffineCompleteVertices.vertexEquiv
            (FlatAffineCompleteRootStages.next (CoordinateDoubleAffinePrefix.inputs (readers P) (depth d)
              (objective d old) (levels P d old level)))
            (CoordinateDoubleAffinePrefix.coneCertificate (readers P) (fun q => depth d q + 1)
              (objective d old) (levels P d old level)) q ⟨w, hw⟩))) := by
  have hchild := CoordinateDoubleAffineChildRecords.heightWord_valid (readers P) (depth d)
    (objective d old) (levels P d old level) q w hw
  have ht := CoordinateDoubleAffineTraceChildConnectivity.reencodeChild_preconnected false P d old level q
    (CoordinateDoubleAffineChildRecords.heightWord (readers P) (depth d) (objective d old)
      (levels P d old level) (LeanCanny.pair q w)) hv hchild
  have hs := CoordinateDoubleAffineChildRecords.heightWord_slice (readers P) (depth d)
    (objective d old) (levels P d old level) q w hw
  have h := ht.trans (Iff.of_eq (congrArg IsPreconnected hs))
  simpa only [heightFrameWord, LeanCanny.pairFst_pair] using h

open CoordinateDoubleAffineTraceHeightRequests in
theorem value_of_ready (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (answer : List Bool → List Bool) (q : List Bool)
    (hq : q ∈ ready P d old level) :
    (program P d old level).value answer q = answer (query P d old level q) := by
  simp only [SingleCall.Program.value, program, hq, decide_true, ite_true, LeanCanny.pairSnd_pair]

end LeanCanny.Connectivity.CoordinateDoubleAffineTraceHeightRequestGeometry
