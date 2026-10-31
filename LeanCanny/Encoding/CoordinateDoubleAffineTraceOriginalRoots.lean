/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceChildWords
public import LeanCanny.Encoding.FlatAffineOriginalSliceTransport

/-! # Decoded original child roots in the uniform trace context -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineCompleteVertices

theorem vertexEquiv_eq_originalRootsEquiv (F : FlatAffineFullSourceTower.Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate F) (u w : List Bool) (hw : Valid F C u w) :
    vertexEquiv F C u ⟨w, hw⟩ = FlatAffinePowerSampleInput.originalRootsEquiv F u
      (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F C) u w hw) := rfl

end LeanCanny.Encoding.FlatAffineCompleteVertices

namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Algebra
open FlatAffinePowerSampleInput (OriginalRoots originalRootsEquiv)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
attribute [local irreducible] objective levels depth append seedCoordinate powerRoot reencodeChild
  originalRootsEquiv FlatAffineCompleteVertices.vertexEquiv SquareSampleCompleteVertices.Valid
  FlatAffineOriginalRootTransport.context FlatAffineOriginalRootTransport.transport
  FlatAffinePowerRootTransport.context FlatAffinePowerRootTransport.transport

noncomputable def extendedOriginalRoot (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (x : OriginalRoots
      (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q) :
    OriginalRoots (extendedInputs midpoint P d old level) q :=
  ⟨x.val, fun i => (congrArg (fun s => (s i).eval₂ (Int.castRingHom ℝ) x.val)
    (extended_system midpoint P d old level q hv)).trans (x.property i)⟩

attribute [local irreducible] extendedOriginalRoot

theorem extendedOriginalRoot_val (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (x : OriginalRoots
      (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q) :
    (extendedOriginalRoot midpoint P d old level q hv x).val = x.val := by
  unfold extendedOriginalRoot
  rfl

noncomputable def originalRoot (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (x : OriginalRoots
      (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q) :
    OriginalRoots (inputs P d old level) (append midpoint q) :=
  FlatAffineOriginalRootTransport.context (inputs P d old level) (append midpoint) q
    (FlatAffineOriginalRootTransport.transport (extendedInputs midpoint P d old level)
      (FlatAffineFullSourceContext.comp (inputs P d old level) (append midpoint))
      (extendedInputs_eq_context midpoint P d old level) q (extendedOriginalRoot midpoint P d old level q hv x))

attribute [local irreducible] originalRoot

theorem equiv_powerRoot (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (x : FlatAffinePowerRootTransport.Roots
      (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q) :
    originalRootsEquiv (inputs P d old level) (append midpoint q) (powerRoot midpoint P d old level q hv x) =
      originalRoot midpoint P d old level q hv (originalRootsEquiv
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q x) := by
  let xp : FlatAffinePowerRootTransport.Roots (extendedInputs midpoint P d old level) q :=
    ⟨x.val, fun i => (congrArg (fun s => (s i).eval₂ (Int.castRingHom ℝ) x.val)
      (extended_power_system midpoint P d old level q hv)).trans (x.property i)⟩
  have HE : originalRootsEquiv (extendedInputs midpoint P d old level) q xp =
      extendedOriginalRoot midpoint P d old level q hv (originalRootsEquiv
        (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q x) := by
    apply Subtype.ext
    have HL := FlatAffinePowerSampleInput.originalRootsEquiv_val (extendedInputs midpoint P d old level) q xp
    have HR0 := extendedOriginalRoot_val midpoint P d old level q hv (originalRootsEquiv
      (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q x)
    have HR := FlatAffinePowerSampleInput.originalRootsEquiv_val
      (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q x
    exact HL.trans (HR0.trans HR).symm
  have H0 := FlatAffineOriginalRootTransport.equiv_context (inputs P d old level) (append midpoint) q
    (FlatAffinePowerRootTransport.transport (extendedInputs midpoint P d old level)
      (FlatAffineFullSourceContext.comp (inputs P d old level) (append midpoint)) (extendedInputs_eq_context midpoint P d old level) q xp)
  have H1 := FlatAffineOriginalRootTransport.equiv_transport (extendedInputs midpoint P d old level)
    (FlatAffineFullSourceContext.comp (inputs P d old level) (append midpoint)) (extendedInputs_eq_context midpoint P d old level) q xp
  unfold powerRoot originalRoot
  exact H0.trans (congrArg (FlatAffineOriginalRootTransport.context (inputs P d old level) (append midpoint) q)
    (H1.trans (congrArg (FlatAffineOriginalRootTransport.transport (extendedInputs midpoint P d old level)
      (FlatAffineFullSourceContext.comp (inputs P d old level) (append midpoint)) (extendedInputs_eq_context midpoint P d old level) q) HE)))

theorem reencodeChild_root (midpoint : Bool) (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool) (hv : Valid P (seedCoordinate d old) q)
    (hw : SquareSampleCompleteVertices.Valid
      (CoordinateDoubleAffineChildRecords.childInput midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q w) :
    FlatAffineCompleteVertices.vertexEquiv (inputs P d old level) (cone P d old level) (append midpoint q)
      ⟨reencodeChild midpoint P d old level (LeanCanny.pair q w), reencodeChild_valid midpoint P d old level q w hv hw⟩ =
      originalRoot midpoint P d old level q hv
        (FlatAffineCompleteVertices.vertexEquiv
          (CoordinateDoubleAffineChildRecords.inputs midpoint (readers P) (depth d) (objective d old) (levels P d old level))
          (CoordinateDoubleAffineChildRecords.cone midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q ⟨w, hw⟩) := by
  let x := SquareSampleCompleteVertices.candidate
    (CoordinateDoubleAffineChildRecords.childInput midpoint (readers P) (depth d) (objective d old) (levels P d old level)) q w hw
  have HP := (reencodeChild_point midpoint P d old level q w hv hw).trans (powerRoot_val midpoint P d old level q hv x).symm
  have HE := congrArg (originalRootsEquiv (inputs P d old level) (append midpoint q)) (Subtype.ext HP)
  rw [FlatAffineCompleteVertices.vertexEquiv_eq_originalRootsEquiv, FlatAffineCompleteVertices.vertexEquiv_eq_originalRootsEquiv]
  exact HE.trans (equiv_powerRoot midpoint P d old level q hv x)

end LeanCanny.Encoding.CoordinateDoubleAffineTrace
