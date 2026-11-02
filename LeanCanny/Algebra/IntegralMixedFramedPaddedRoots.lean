/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPaddedStep
public import LeanCanny.Algebra.UniformIntegralPrefixJointRoots
/-! # Actual padded-history joint roots retain their literal parent tail -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open IntegralMixedHistory UniformIntegralPrefix

variable {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem padded_roots_parent (x : State P S B 0 ι) (default : Instruction n B)
    (cs : List (Instruction n B)) (birth : ℕ) (hb : birth≤S) (z : ℕ→ℝ)
    (hz : RootsAt (run x (paddedPast default cs (birth+1)) (by rw [paddedPast_length]; omega)).sampler.scalarPrefix z) :
    RootsAt (run x (paddedPast default cs birth) (by rw [paddedPast_length]; omega)).sampler.scalarPrefix
      (fun i=>z (i+1)) := by
  have HD : (paddedPast default cs (birth+1)).length=(paddedPast default cs birth).length+1 := by
    rw [paddedPast_length,paddedPast_length]
  have HS:=padded_step_prefix x default cs birth hb
  have HR:=(rootsAt_heq _ _ rfl rfl HD HS z).mp hz
  exact rootsAt_parent _ _ _ _ _ _ HR

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript
