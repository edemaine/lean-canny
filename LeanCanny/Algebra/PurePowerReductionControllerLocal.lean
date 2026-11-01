/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PurePowerReductionController
/-! # Reduction correctness from the single guarded child reply

Bounded flat writers need not preserve arbitrary oversized query packets.
Only the actual requested packet is charged in this local correctness rule.
-/
@[expose] public section
namespace LeanCanny.Algebra.PurePowerReductionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] negate sourceQuery
theorem program_value_at (L : Layout) (bound : List Bool → ℕ) (constant coefficient input task answer : List Bool → List Bool)
    (p : List Bool)
    (he : request L bound (input p) →
      answer (task (sourceQuery L (input p))) = coefficient (sourceQuery L (input p))) :
    (program L bound constant input task).value answer p = entry L bound constant coefficient (input p) := by
  by_cases hn : normal L (input p)
  · simp only [SingleCall.Program.value, program, request, hn, not_true_eq_false, false_and,
      decide_false, Bool.false_eq_true, ite_false, immediate, true_and, entry, ite_true]
  · by_cases hv : valid L bound (input p)
    · by_cases ha : admissible L (input p)
      · have hr : request L bound (input p) := ⟨hn, hv, ha⟩
        simp only [SingleCall.Program.value, program, show decide (request L bound (input p)) = true from decide_eq_true hr,
          ite_true, finish, pairFst_pair, pairSnd_pair, he hr, entry, hn, ite_false, hv, ha]
      · have hr : ¬ request L bound (input p) := fun h => ha h.2.2
        simp only [SingleCall.Program.value, program, show decide (request L bound (input p)) = false from decide_eq_false hr,
          Bool.false_eq_true, ite_false, immediate, hn, false_and, entry, hv, ha, ite_true]
    · have hr : ¬ request L bound (input p) := fun h => hv h.2.1
      simp only [SingleCall.Program.value, program, show decide (request L bound (input p)) = false from decide_eq_false hr,
        Bool.false_eq_true, ite_false, immediate, hn, false_and, entry, hv]

end LeanCanny.Algebra.PurePowerReductionBits
