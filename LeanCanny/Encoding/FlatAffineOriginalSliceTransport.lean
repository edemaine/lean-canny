/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineOriginalRootTransport
public import LeanCanny.Encoding.FlatAffineSlicePresentation

/-! # Original affine slices under input and source-context transport -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineOriginalRootTransport
open LeanCanny.Algebra
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open FlatAffinePowerSampleInput (OriginalRoots)
set_option backward.isDefEq.respectTransparency false

theorem transport_mem_slice (F G : Inputs) (h : F = G) (u : List Bool) (x : OriginalRoots F u)
    (y : Fin (arity G u) → ℝ) :
    y ∈ FlatAffineCompleteComponentSamples.slice G u (transport F G h u x) ↔
      (y ∘ Fin.cast (congrArg (fun H : Inputs => arity H u) h)) ∈ FlatAffineCompleteComponentSamples.slice F u x := by
  subst G
  rfl

theorem context_slice (F : Inputs) (f : List Bool → List Bool) (u : List Bool)
    (x : OriginalRoots (FlatAffineFullSourceContext.comp F f) u) :
    FlatAffineCompleteComponentSamples.slice F (f u) (context F f u x) =
      FlatAffineCompleteComponentSamples.slice (FlatAffineFullSourceContext.comp F f) u x := by
  have HS := FlatAffineFullSourceContext.free_comp F f u (F.depth (f u))
  have HA := funext (fun j : Fin (arity F (f u)) => funext (fun i : Fin (arity F (f u)) =>
    FlatAffineFullSourceContext.direction_comp F f u (F.depth (f u)) j.succ i))
  have HB := funext (fun j : Fin (arity F (f u)) => congrArg
    (fun b : FlatAffineCriticalTower.Level (arity F (f u)) (F.depth (f u)) ℤ =>
      b.polynomial.eval₂ (Int.castRingHom ℝ)
        (x.val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F (f u)) (F.depth (f u))))
    (FlatAffineFullSourceContext.level_comp F f u (F.depth (f u)) j))
  rw [FlatAffineSlicePresentation.original, FlatAffineSlicePresentation.original,
    context_val, FlatAffineFullSourceContext.polynomial_comp]
  exact (FlatAffineSlicePresentation.set_congr (BoundedFullCriticalSamples.polynomial F.source (f u)) HS HA HB).symm

end LeanCanny.Encoding.FlatAffineOriginalRootTransport
