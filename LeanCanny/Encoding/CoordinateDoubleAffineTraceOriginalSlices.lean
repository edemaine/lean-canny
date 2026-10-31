/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceOriginalRoots

/-! # Exact original spatial slices of re-encoded coordinate children -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSlicePresentation
open LeanCanny.Algebra
set_option backward.isDefEq.respectTransparency false

theorem original_value (F : FlatAffineFullSourceTower.Inputs) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (z : Fin (FlatAffineFullSourceTower.count F u) → ℝ) (hz : x.val = z) :
    FlatAffineCompleteComponentSamples.slice F u x =
      set (BoundedFullCriticalSamples.polynomial F.source u)
        (FlatAffineFullSourceTower.free F u (F.depth u))
        (fun j i => FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i)
        (fun j => (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial.eval₂ (Int.castRingHom ℝ)
          (z ∘ TriangularPolynomialIndexing.enumerate (FlatAffineFullSourceTower.stageWidth F u) (F.depth u))) := by
  rw [original, hz]

end LeanCanny.Encoding.FlatAffineSlicePresentation

namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Algebra
open FlatAffineFullSourceTower (arity stageWidth)
open FlatAffinePowerSampleInput (OriginalRoots)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] objective levels depth append seedCoordinate originalRoot extendedOriginalRoot reencodeChild
  FlatAffineCompleteComponentSamples.slice FlatAffineCompleteVertices.vertexEquiv SquareSampleCompleteVertices.Valid
  FlatAffineFullSourceTower.free FlatAffineFullSourceTower.direction FlatAffineFullSourceTower.level
  FlatAffineSlicePresentation.set

def ambientIndex (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) :
    Fin ((readers P).dim q + 4) → Fin (arity (inputs P d old level) (append midpoint q)) :=
  Fin.cast (congrArg (fun F : FlatAffineFullSourceTower.Inputs => arity F q) (extendedInputs_eq_context midpoint P d old level))

theorem ambientIndex_val (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (i : Fin ((readers P).dim q + 4)) :
    (ambientIndex midpoint P d old level q i).val = i.val := rfl

theorem extendedOriginal_slice (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (x : OriginalRoots
      (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q) :
    FlatAffineCompleteComponentSamples.slice (extendedInputs midpoint P d old level) q
      (extendedOriginalRoot midpoint P d old level q hv x) =
      FlatAffineCompleteComponentSamples.slice
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q x := by
  let k := CoordinateDoubleAffineChildRecords.childDepth midpoint (depth d) q
  have hk : k ≤ depth d (append midpoint q) := by rw [depth_append]; rfl
  have HS := extended_free midpoint P d old level q k hk
  have HA := funext (fun j : Fin ((readers P).dim q + 4) => funext (fun i : Fin ((readers P).dim q + 4) =>
    congrFun (congrFun (extended_direction midpoint P d old level q k hk) j.succ) i))
  have HB := funext (fun j : Fin ((readers P).dim q + 4) => congrArg
    (fun b : FlatAffineCriticalTower.Level ((readers P).dim q + 4) k ℤ =>
      b.polynomial.eval₂ (Int.castRingHom ℝ)
        (x.val ∘ TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width ((readers P).dim q + 4)) k))
    (extended_level midpoint P d old level q k hv hk j))
  have H0 := FlatAffineSlicePresentation.original_value (extendedInputs midpoint P d old level) q
    (extendedOriginalRoot midpoint P d old level q hv x) x.val (extendedOriginalRoot_val midpoint P d old level q hv x)
  have H1 := FlatAffineSlicePresentation.set_congr (BoundedFullCriticalSamples.polynomial (readers P) q) HS HA HB
  have H2 := FlatAffineSlicePresentation.original
    (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q x
  exact H0.trans (H1.trans H2.symm)

theorem originalRoot_mem_slice (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (x : OriginalRoots
      (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q)
    (y : Fin (arity (inputs P d old level) (append midpoint q)) → ℝ) :
    y ∈ FlatAffineCompleteComponentSamples.slice (inputs P d old level) (append midpoint q)
      (originalRoot midpoint P d old level q hv x) ↔
      (y ∘ ambientIndex midpoint P d old level q) ∈ FlatAffineCompleteComponentSamples.slice
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q x := by
  let xe := extendedOriginalRoot midpoint P d old level q hv x
  let xc := FlatAffineOriginalRootTransport.transport (extendedInputs midpoint P d old level)
    (FlatAffineFullSourceContext.comp (inputs P d old level) (append midpoint)) (extendedInputs_eq_context midpoint P d old level) q xe
  have HC := congrArg (fun S : Set (Fin (arity (inputs P d old level) (append midpoint q)) → ℝ) => y ∈ S)
    (FlatAffineOriginalRootTransport.context_slice (inputs P d old level) (append midpoint) q xc)
  have HT := FlatAffineOriginalRootTransport.transport_mem_slice (extendedInputs midpoint P d old level)
    (FlatAffineFullSourceContext.comp (inputs P d old level) (append midpoint)) (extendedInputs_eq_context midpoint P d old level) q xe y
  have HS := congrArg (fun S : Set (Fin ((readers P).dim q + 4) → ℝ) => (y ∘ ambientIndex midpoint P d old level q) ∈ S)
    (extendedOriginal_slice midpoint P d old level q hv x)
  unfold originalRoot
  exact (Iff.of_eq HC).trans (HT.trans (Iff.of_eq HS))

theorem reencodeChild_mem_slice (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (hw : SquareSampleCompleteVertices.Valid
      (CoordinateDoubleAffineChildRecords.childInput midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q w)
    (y : Fin (arity (inputs P d old level) (append midpoint q)) → ℝ) :
    y ∈ FlatAffineCompleteComponentSamples.slice (inputs P d old level) (append midpoint q)
      (FlatAffineCompleteVertices.vertexEquiv (inputs P d old level) (cone P d old level) (append midpoint q)
        ⟨reencodeChild midpoint P d old level (LeanCanny.pair q w), reencodeChild_valid midpoint P d old level q w hv hw⟩) ↔
      (y ∘ ambientIndex midpoint P d old level q) ∈ FlatAffineCompleteComponentSamples.slice
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q
        (FlatAffineCompleteVertices.vertexEquiv
          (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level))
          (CoordinateDoubleAffineChildRecords.cone midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q ⟨w, hw⟩) := by
  have H := congrArg (fun r => y ∈ FlatAffineCompleteComponentSamples.slice (inputs P d old level) (append midpoint q) r)
    (reencodeChild_root midpoint P d old level q w hv hw)
  exact (Iff.of_eq H).trans (originalRoot_mem_slice midpoint P d old level q hv _ y)

end LeanCanny.Encoding.CoordinateDoubleAffineTrace
