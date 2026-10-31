/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralReductionActionCorrect
public import LeanCanny.Algebra.IntegralBerkowitzBlockSpace

/-! # Native relative characteristic coefficients of constructed reduction actions

The characteristic matrix is constructed by powering the original
algebra-valued reduction matrix and selecting its shifted normal columns.
Neither the action nor its characteristic coefficients are supplied as
reader oracles. Only the original reduction-entry program is charged.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralReductionActionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] IntegralBlockPowerBits.Family.value

theorem entry_evaluator (S : Source) (a : IntegralBerkowitzBlockBits.Access S.toSource)
    (h : Controls S) (E : SpaceFunction a.entry) : SpaceFunction (entryProgram S) := by
  have P := power_evaluator S a h E
  have Z := SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])
  exact (SpaceFunction.branch (fun p => decide (normalGuard S p)) h.normal.flag_mem_FP P Z).congr
    (funext fun _ => by simp only [entryProgram, decide_eq_true_eq])

noncomputable def actionAccess (S : Source) (a : IntegralBerkowitzBlockBits.Access S.toSource) :
    IntegralBerkowitzBlockBits.Access (actionSource S) where
  dimension := a.dimension
  rank := a.rank
  modulus := a.modulus
  coefficient := a.coefficient
  basisRow := a.basisRow
  basisCol := a.basisCol
  entry := entryProgram S
  entry_eq := entry_correct S

attribute [local irreducible] entryProgram IntegralBerkowitzBlockBits.Source.value

theorem evaluator (S : Source) (a : IntegralBerkowitzBlockBits.Access S.toSource)
    (h : Controls S) (E : SpaceFunction a.entry) : SpaceFunction (actionSource S).value := by
  have HE : SpaceFunction (actionAccess S a).entry := by
    change SpaceFunction (entryProgram S)
    exact entry_evaluator S a h E
  exact IntegralBerkowitzBlockBits.evaluator (actionSource S) (actionAccess S a) HE

end LeanCanny.Algebra.IntegralReductionActionBits
