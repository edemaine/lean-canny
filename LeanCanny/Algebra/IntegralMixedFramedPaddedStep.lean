/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistorySuccessor
/-! # Literal scalar-prefix recurrence at the next actual framed instruction

The next normalized row is computed in the actual old algebra after
reframing to its own source. Existing instructions are never replayed at
the new source. The identity also covers beyond-end default instructions.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open IntegralMixedHistory

variable {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem padded_step_prefix (x : State P S B 0 ι) (default : Instruction n B)
    (cs : List (Instruction n B)) (birth : ℕ) (hb : birth≤S) :
    HEq (run x (paddedPast default cs (birth+1)) (by rw [paddedPast_length]; omega)).sampler.scalarPrefix
      (UniformIntegralPrefix.step
        (run x (paddedPast default cs birth) (by rw [paddedPast_length]; omega)).sampler.scalarPrefix
        (by rw [paddedPast_length]; exact hb) (Nat.two_pow_pos B)
        (IntegralMixedFullHistoryScript.polynomial
          (reframe (run x (paddedPast default cs birth) (by rw [paddedPast_length]; omega))
            ((chronological cs birth).getD default).source ((chronological cs birth).getD default).source_cap)
          (by rw [paddedPast_length]; exact hb) ((chronological cs birth).getD default).command)
        (IntegralMixedFullHistoryScript.degree
          (reframe (run x (paddedPast default cs birth) (by rw [paddedPast_length]; omega))
            ((chronological cs birth).getD default).source ((chronological cs birth).getD default).source_cap)
          (by rw [paddedPast_length]; exact hb) ((chronological cs birth).getD default).command)) := by
  exact (padded_run_successor x default cs birth hb _).trans
    (heq_of_eq (run_prefix x ((chronological cs birth).getD default) (paddedPast default cs birth) _))

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript
