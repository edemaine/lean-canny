/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceOriginalSlices

/-! # Child connectivity is preserved in the uniform native trace family -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineOriginalRootTransport
open Set
open FlatAffineFullSourceTower (Inputs)
open FlatAffinePowerSampleInput (OriginalRoots)
set_option backward.isDefEq.respectTransparency false

theorem transport_preconnected (F G : Inputs) (h : F = G) (u : List Bool) (x : OriginalRoots F u) :
    IsPreconnected (FlatAffineCompleteComponentSamples.slice G u (transport F G h u x)) ↔
      IsPreconnected (FlatAffineCompleteComponentSamples.slice F u x) := by
  subst G
  rfl


theorem transport_joined (F G : Inputs) (h : F = G) (u : List Bool) (x : OriginalRoots F u)
    (y z : Fin (FlatAffineFullSourceTower.arity G u) → ℝ) :
    JoinedIn (FlatAffineCompleteComponentSamples.slice G u (transport F G h u x)) y z ↔
      JoinedIn (FlatAffineCompleteComponentSamples.slice F u x)
        (y ∘ Fin.cast (congrArg (fun H : Inputs => FlatAffineFullSourceTower.arity H u) h))
        (z ∘ Fin.cast (congrArg (fun H : Inputs => FlatAffineFullSourceTower.arity H u) h)) := by
  subst G
  rfl

end LeanCanny.Encoding.FlatAffineOriginalRootTransport

namespace LeanCanny.Connectivity.CoordinateDoubleAffineTraceChildConnectivity
open Set LeanCanny.Algebra LeanCanny.Encoding
open CoordinateDoubleAffineTrace
open FlatAffinePowerSampleInput (OriginalRoots)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] objective levels depth append seedCoordinate originalRoot extendedOriginalRoot reencodeChild
  FlatAffineCompleteComponentSamples.slice FlatAffineCompleteVertices.vertexEquiv SquareSampleCompleteVertices.Valid

theorem originalRoot_preconnected (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (x : OriginalRoots
      (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q) :
    IsPreconnected (FlatAffineCompleteComponentSamples.slice (inputs P d old level) (append midpoint q)
      (originalRoot midpoint P d old level q hv x)) ↔
      IsPreconnected (FlatAffineCompleteComponentSamples.slice
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q x) := by
  let xe := extendedOriginalRoot midpoint P d old level q hv x
  let xc := FlatAffineOriginalRootTransport.transport (extendedInputs midpoint P d old level)
    (FlatAffineFullSourceContext.comp (inputs P d old level) (append midpoint)) (extendedInputs_eq_context midpoint P d old level) q xe
  have HC := congrArg IsPreconnected (FlatAffineOriginalRootTransport.context_slice (inputs P d old level) (append midpoint) q xc)
  have HT := FlatAffineOriginalRootTransport.transport_preconnected (extendedInputs midpoint P d old level)
    (FlatAffineFullSourceContext.comp (inputs P d old level) (append midpoint)) (extendedInputs_eq_context midpoint P d old level) q xe
  have HS := congrArg IsPreconnected (extendedOriginal_slice midpoint P d old level q hv x)
  unfold originalRoot
  exact (Iff.of_eq HC).trans (HT.trans (Iff.of_eq HS))

theorem reencodeChild_preconnected (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (hw : SquareSampleCompleteVertices.Valid
      (CoordinateDoubleAffineChildRecords.childInput midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q w) :
    IsPreconnected (FlatAffineCompleteComponentSamples.slice (inputs P d old level) (append midpoint q)
      (FlatAffineCompleteVertices.vertexEquiv (inputs P d old level) (cone P d old level) (append midpoint q)
        ⟨reencodeChild midpoint P d old level (LeanCanny.pair q w), reencodeChild_valid midpoint P d old level q w hv hw⟩)) ↔
      IsPreconnected (FlatAffineCompleteComponentSamples.slice
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q
        (FlatAffineCompleteVertices.vertexEquiv
          (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level))
          (CoordinateDoubleAffineChildRecords.cone midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q ⟨w, hw⟩)) := by
  have H := congrArg (fun r => IsPreconnected (FlatAffineCompleteComponentSamples.slice (inputs P d old level) (append midpoint q) r))
    (reencodeChild_root midpoint P d old level q w hv hw)
  exact (Iff.of_eq H).trans (originalRoot_preconnected midpoint P d old level q hv _)


theorem originalRoot_joined (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (x : OriginalRoots
      (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q)
    (y z : Fin (FlatAffineFullSourceTower.arity (inputs P d old level) (append midpoint q)) → ℝ) :
    JoinedIn (FlatAffineCompleteComponentSamples.slice (inputs P d old level) (append midpoint q)
      (originalRoot midpoint P d old level q hv x)) y z ↔
      JoinedIn (FlatAffineCompleteComponentSamples.slice
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q x)
        (y ∘ ambientIndex midpoint P d old level q) (z ∘ ambientIndex midpoint P d old level q) := by
  let xe := extendedOriginalRoot midpoint P d old level q hv x
  let xc := FlatAffineOriginalRootTransport.transport (extendedInputs midpoint P d old level)
    (FlatAffineFullSourceContext.comp (inputs P d old level) (append midpoint)) (extendedInputs_eq_context midpoint P d old level) q xe
  have HC := congrArg (fun S => JoinedIn S y z)
    (FlatAffineOriginalRootTransport.context_slice (inputs P d old level) (append midpoint) q xc)
  have HT := FlatAffineOriginalRootTransport.transport_joined (extendedInputs midpoint P d old level)
    (FlatAffineFullSourceContext.comp (inputs P d old level) (append midpoint)) (extendedInputs_eq_context midpoint P d old level) q xe y z
  have HS := congrArg (fun S => JoinedIn S (y ∘ ambientIndex midpoint P d old level q) (z ∘ ambientIndex midpoint P d old level q))
    (extendedOriginal_slice midpoint P d old level q hv x)
  unfold originalRoot
  exact (Iff.of_eq HC).trans (HT.trans (Iff.of_eq HS))

theorem reencodeChild_joined (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (hw : SquareSampleCompleteVertices.Valid
      (CoordinateDoubleAffineChildRecords.childInput midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q w)
    (y z : Fin (FlatAffineFullSourceTower.arity (inputs P d old level) (append midpoint q)) → ℝ) :
    JoinedIn (FlatAffineCompleteComponentSamples.slice (inputs P d old level) (append midpoint q)
      (FlatAffineCompleteVertices.vertexEquiv (inputs P d old level) (cone P d old level) (append midpoint q)
        ⟨reencodeChild midpoint P d old level (LeanCanny.pair q w), reencodeChild_valid midpoint P d old level q w hv hw⟩)) y z ↔
      JoinedIn (FlatAffineCompleteComponentSamples.slice
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q
        (FlatAffineCompleteVertices.vertexEquiv
          (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level))
          (CoordinateDoubleAffineChildRecords.cone midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q ⟨w, hw⟩))
        (y ∘ ambientIndex midpoint P d old level q) (z ∘ ambientIndex midpoint P d old level q) := by
  have H := congrArg (fun r => JoinedIn (FlatAffineCompleteComponentSamples.slice (inputs P d old level) (append midpoint q) r) y z)
    (reencodeChild_root midpoint P d old level q w hv hw)
  exact (Iff.of_eq H).trans (originalRoot_joined midpoint P d old level q hv _ y z)

end LeanCanny.Connectivity.CoordinateDoubleAffineTraceChildConnectivity
