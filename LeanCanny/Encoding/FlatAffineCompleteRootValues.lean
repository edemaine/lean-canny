/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineCompleteRootStages

/-! # The actual point stored by a complete critical-stage extension -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineCompleteRootStages
open LeanCanny.Algebra
open FlatAffineFullSourceTower (Inputs arity)

theorem extend_val (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (y : FlatAffineCriticalStage.Variables (arity F u) → ℝ) (hy) :
    (extend F u x y hy).val = FlatAffineTowerRegularity.appendPoint (F.depth u) x.val y := rfl

end LeanCanny.Encoding.FlatAffineCompleteRootStages
