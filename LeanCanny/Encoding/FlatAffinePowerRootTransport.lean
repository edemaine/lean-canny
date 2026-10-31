/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerSampleInput

/-! # Transporting powered roots without identifying native vertex words -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerRootTransport
open LeanCanny.Algebra
open FlatAffineFullSourceTower (Inputs)
set_option backward.isDefEq.respectTransparency false

abbrev Roots (F : Inputs) (u : List Bool) :=
  {z : Fin (FlatAffineFullSourcePositive.count F u) → ℝ //
    ∀ i, (FlatAffinePowerPositive.system F u i).eval₂ (Int.castRingHom ℝ) z = 0}

noncomputable def transport (F G : Inputs) (h : F = G) (u : List Bool) (x : Roots F u) : Roots G u := h ▸ x

theorem transport_val (F G : Inputs) (h : F = G) (u : List Bool) (x : Roots F u) :
    (transport F G h u x).val = x.val ∘ Fin.cast (congrArg (fun H : Inputs => FlatAffineFullSourcePositive.count H u) h).symm := by
  subst G
  rfl

noncomputable def context (F : Inputs) (f : List Bool → List Bool) (u : List Bool)
    (x : Roots (FlatAffineFullSourceContext.comp F f) u) : Roots F (f u) :=
  ⟨x.val, fun i =>
    (congrArg (fun p => p.eval₂ (Int.castRingHom ℝ) x.val) (FlatAffinePowerPositive.system_comp F f u i)).symm.trans (x.property i)⟩

attribute [local irreducible] context

theorem context_val (F : Inputs) (f : List Bool → List Bool) (u : List Bool)
    (x : Roots (FlatAffineFullSourceContext.comp F f) u) : (context F f u x).val = x.val := by
  unfold context
  rfl

end LeanCanny.Encoding.FlatAffinePowerRootTransport
