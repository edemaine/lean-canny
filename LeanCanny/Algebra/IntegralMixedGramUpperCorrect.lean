/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramUpperDispatcher
/-! # All Gram determinant internal replies close against its actual model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramUpperDispatcher
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedGramUpperBits IntegralMixedGramUpperModel
open scoped Classical

theorem action_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) (own : Matches P F answer) :
    ActionMatches P F answer := by
  intro q hv hr hp
  change phase q = 19 at hp
  have H := own q hv hr (Or.inl hp)
  rw [hp] at H
  exact H.trans (IntegralMixedGramMatrixModel.action_native P F q).symm

theorem moment_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) (own : Matches P F answer) :
    MomentMatches P F answer := by
  intro q hv hr hp
  change phase q = 21 at hp
  have H := own q hv hr (Or.inr (Or.inl hp))
  rw [hp] at H
  exact H

theorem moment_power_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) (own : Matches P F answer) :
    MomentPowerMatches P F answer := by
  intro q hv hr hp
  change phase q = 22 at hp
  have H := own q hv hr (Or.inr (Or.inr (Or.inl hp)))
  rw [hp] at H
  exact H

theorem factor_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) (own : Matches P F answer) :
    FactorMatches P F answer := by
  intro q hv hr hp
  change phase q = 23 at hp
  have H := own q hv hr (Or.inr (Or.inr (Or.inr (Or.inl hp))))
  rw [hp] at H
  exact H

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (rows : IntegralMixedValueRowModel.Matches P F (fun q => residueBits (x q)))
    (own : Matches P F (fun q => residueBits (x q))) :
    Correct (machine P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  have H19 := IntegralMixedGramBlockEntryNative.correct_of_rows P a F h _ rows
  have H21 := correct21 P a F h g x (action_matches P F _ own)
  have H22 := correct22_of_matches P a F h g _ (moment_matches P F _ own)
  have H23 := correct23 P a F h g x (action_matches P F _ own) (moment_power_matches P F _ own)
  have H24 := correct24 P a F h g _ (factor_matches P F _ own)
  unfold machine
  apply choose_correct _ _ _ _ H19
  apply choose_correct _ _ _ _ H21
  apply choose_correct _ _ _ _ H22
  apply choose_correct _ _ _ _ H23
  apply choose_correct _ _ _ _ H24
  exact zero_correct _ _

end LeanCanny.Algebra.IntegralMixedGramUpperDispatcher
