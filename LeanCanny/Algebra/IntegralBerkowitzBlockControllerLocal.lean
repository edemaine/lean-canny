/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralBerkowitzBlockController
/-! # Relative-factor correctness from the actual guarded reply -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralBerkowitzBlockBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] selector negative oneWord IntegralBlockMomentBits.Family.value
theorem program_value_at (S : Source) (a : Access S) (diagonalTask momentTask answer : List Bool → List Bool)
    (p : List Bool)
    (hd : selector S p = [false, true] → answer (diagonalTask (diagonalQuery S p)) = a.entry (diagonalQuery S p))
    (hm : selector S p = [true, true] → answer (momentTask p) = (momentFamily S).value p) : (program S diagonalTask momentTask).value answer p = factorValue S a p := by
  change (if decide (request S p) then negative S (pair p (answer (child S diagonalTask momentTask p)))
    else immediate S p) = factorValue S a p
  by_cases hu : selector S p = [true]
  · have hn : ¬ request S p := by rw [request, hu]; decide
    rw [show decide (request S p) = false from decide_eq_false hn]
    simp only [Bool.false_eq_true, ite_false, immediate, factorValue, hu, ite_true]
  · by_cases hd' : selector S p = [false, true]
    · have hn : request S p := Or.inl hd'
      rw [show decide (request S p) = true from decide_eq_true hn]
      simp only [ite_true]
      unfold child
      rw [ite_eq_left hd', hd hd']
      unfold factorValue
      rw [ite_eq_right hu, ite_eq_left hd']
    · by_cases hm' : selector S p = [true, true]
      · have hn : request S p := Or.inr hm'
        rw [show decide (request S p) = true from decide_eq_true hn]
        simp only [ite_true]
        unfold child
        rw [ite_eq_right hd', hm hm']
        unfold factorValue
        rw [ite_eq_right hu, ite_eq_right hd', ite_eq_left hm']
      · have hn : ¬ request S p := by simp only [request, hd', hm', or_self, not_false_eq_true]
        rw [show decide (request S p) = false from decide_eq_false hn]
        simp only [Bool.false_eq_true, ite_false, immediate, factorValue, hu, hd', hm']

theorem entryController_value_at (S : Source) (a : Access S) (diagonalTask momentTask answer : List Bool → List Bool)
    (q : List Bool)
    (hd : selector S (outerPacket S q) = [false, true] →
      answer (diagonalTask (diagonalQuery S (outerPacket S q))) = a.entry (diagonalQuery S (outerPacket S q)))
    (hm : selector S (outerPacket S q) = [true, true] →
      answer (momentTask (outerPacket S q)) = (momentFamily S).value (outerPacket S q)) :
    (entryController S diagonalTask momentTask).value answer q = entryProgram S a q := by
  have H := program_value_at S a diagonalTask momentTask answer (outerPacket S q) hd hm
  simpa only [SingleCall.Program.value, entryController, program, pairFst_pair, pairSnd_pair,
    entryProgram, Function.comp_apply] using H
end LeanCanny.Algebra.IntegralBerkowitzBlockBits
