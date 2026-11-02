/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscContextUpperDispatcher
/-! # Every internal PSC determinant reply closes against its actual model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscContextUpperDispatcher
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedPscContextUpperBits IntegralMixedPscContextUpperModel
open scoped Classical

theorem project (P : Parameters) (F : Family) (answer : List Bool → List Bool) (own : Matches P F answer)
    (p : Phase) (hp : p.code ≤ 4) (q : List Bool) (hs : selected P F p q = true) :
    answer q = component P F p.code q := by
  have HH := (selected_iff P F p q).mp hs
  have HP := HH.2
  change phase q = p.code at HP
  have H := own q HH.1 (by omega)
  rw [HP] at H
  exact H

theorem action_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) (own : Matches P F answer) :
    ActionMatches P F answer := by
  intro q hs
  exact (project P F answer own .originalCoefficient (by decide) q hs).trans
    (IntegralMixedPscMatrixModel.action_native P F q).symm

theorem entry_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) (own : Matches P F answer) :
    MomentEntryMatches P F answer := by
  intro q hs
  exact project P F answer own .derivativeCoefficient (by decide) q hs

theorem moment_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) (own : Matches P F answer) :
    MomentPowerMatches P F answer := by
  intro q hs
  exact project P F answer own .clearedHeight (by decide) q hs

attribute [local irreducible] IntegralMixedPscUpperBits.factorValue

theorem factor_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) (own : Matches P F answer) :
    FactorMatches P F answer := by
  intro q hs
  exact project P F answer own .monomialFactor (by decide) q hs

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (entries : IntegralMixedPscContextActionBits.EntryMatches P F (fun q => residueBits (x q)))
    (own : Matches P F (fun q => residueBits (x q))) :
    Correct (machine P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  have H0 := IntegralMixedPscContextActionBits.correct_of_matches P a F h _ entries
  have H1 := correct1 P a F h g x (action_matches P F _ own)
  have H2 := correct2 P a F h g _ (entry_matches P F _ own)
  have H3 := correct3 P a F h g x (action_matches P F _ own) (moment_matches P F _ own)
  have H4 := correct4 P a F h g _ (factor_matches P F _ own)
  unfold machine
  apply choose_correct _ _ _ _ H0
  apply choose_correct _ _ _ _ H1
  apply choose_correct _ _ _ _ H2
  apply choose_correct _ _ _ _ H3
  apply choose_correct _ _ _ _ H4
  exact zero_correct _ _

end LeanCanny.Algebra.IntegralMixedPscContextUpperDispatcher
