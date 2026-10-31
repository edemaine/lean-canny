/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerRootTransport
public import LeanCanny.Encoding.FlatAffinePowerOriginalSamples

/-! # Original roots commute with input and source-context transport -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerSampleInput
open LeanCanny.Algebra

theorem originalRootsEquiv_val (F : FlatAffineFullSourceTower.Inputs) (u : List Bool)
    (x : FlatAffinePowerRootTransport.Roots F u) :
    (originalRootsEquiv F u x).val = FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree F u)
      (x.val ∘ Fin.castSucc) := rfl

end LeanCanny.Encoding.FlatAffinePowerSampleInput

namespace LeanCanny.Encoding.FlatAffineOriginalRootTransport
open LeanCanny.Algebra
open FlatAffineFullSourceTower (Inputs)
open FlatAffinePowerSampleInput (OriginalRoots originalRootsEquiv)
set_option backward.isDefEq.respectTransparency false

noncomputable def transport (F G : Inputs) (h : F = G) (u : List Bool) (x : OriginalRoots F u) : OriginalRoots G u := h ▸ x

theorem transport_val (F G : Inputs) (h : F = G) (u : List Bool) (x : OriginalRoots F u) :
    (transport F G h u x).val = x.val ∘ Fin.cast (congrArg (fun H : Inputs => FlatAffineFullSourceTower.count H u) h).symm := by
  subst G
  rfl

noncomputable def context (F : Inputs) (f : List Bool → List Bool) (u : List Bool)
    (x : OriginalRoots (FlatAffineFullSourceContext.comp F f) u) : OriginalRoots F (f u) :=
  ⟨x.val, fun i =>
    (congrArg (fun p => p.eval₂ (Int.castRingHom ℝ) x.val) (FlatAffineFullSourceContext.system_comp F f u i)).symm.trans (x.property i)⟩

attribute [local irreducible] context

theorem context_val (F : Inputs) (f : List Bool → List Bool) (u : List Bool)
    (x : OriginalRoots (FlatAffineFullSourceContext.comp F f) u) : (context F f u x).val = x.val := by
  unfold context
  rfl

theorem equiv_transport (F G : Inputs) (h : F = G) (u : List Bool) (x : FlatAffinePowerRootTransport.Roots F u) :
    originalRootsEquiv G u (FlatAffinePowerRootTransport.transport F G h u x) =
      transport F G h u (originalRootsEquiv F u x) := by
  subst G
  rfl

theorem equiv_context (F : Inputs) (f : List Bool → List Bool) (u : List Bool)
    (x : FlatAffinePowerRootTransport.Roots (FlatAffineFullSourceContext.comp F f) u) :
    originalRootsEquiv F (f u) (FlatAffinePowerRootTransport.context F f u x) =
      context F f u (originalRootsEquiv (FlatAffineFullSourceContext.comp F f) u x) := by
  apply Subtype.ext
  simp only [FlatAffinePowerSampleInput.originalRootsEquiv_val, context_val, FlatAffinePowerRootTransport.context_val]
  rfl

end LeanCanny.Encoding.FlatAffineOriginalRootTransport
