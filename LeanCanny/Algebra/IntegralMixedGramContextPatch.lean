/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramRequestContexts
public import LeanCanny.Algebra.IntegralMixedValueRowContextPatch
/-! # A typed mathematical Gram oracle outside virtual creating contexts -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramScopedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualCaps
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def PhaseAllowed (q : List Bool) : Prop := phase q = 19 ∨ phase q = 21 ∨ phase q = 22 ∨ phase q = 23 ∨ phase q = 24
abbrev Rows (P : Parameters) (F : Family) := IntegralMixedValueRowScopedBits.Matches P F
abbrev Matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, valid P q → IntegralMixedRoutineTaskBits.routine P q = 3 → PhaseAllowed q →
    IntegralMixedVirtualContextBits.context P q → answer q = IntegralMixedGramUpperModel.component P F (phase q) q

noncomputable def patch (P : Parameters) (F : Family) (x : (q : List Bool) → ZMod (modulus P q)) (q : List Bool) : ZMod (modulus P q) :=
  if IntegralMixedVirtualContextBits.context P q then x q else
  if IntegralMixedRoutineTaskBits.routine P q = 3 then Classical.choose (IntegralMixedGramUpperModel.canonical P F q) else
  if IntegralMixedRoutineTaskBits.routine P q = 2 then Classical.choose (IntegralMixedValueRowModel.canonical P F q) else x q

theorem patch_good (P : Parameters) (F : Family) (x : (q : List Bool) → ZMod (modulus P q))
    (q : List Bool) (hc : IntegralMixedVirtualContextBits.context P q) : patch P F x q = x q := by simp only [patch, ite_eq_left hc]

theorem patch_matches (P : Parameters) (F : Family) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : Matches P F (fun q => residueBits (x q))) : IntegralMixedGramUpperModel.Matches P F (fun q => residueBits (patch P F x q)) := by
  intro q hv hr hp
  dsimp only
  by_cases hc : IntegralMixedVirtualContextBits.context P q
  · rw [patch_good P F x q hc]
    exact hm q hv hr hp hc
  · simp only [patch, ite_eq_right hc, ite_eq_left hr]
    exact (Classical.choose_spec (IntegralMixedGramUpperModel.canonical P F q)).trans
      (IntegralMixedGramUpperModel.value_matches P F q hv hr hp)

theorem patch_rows (P : Parameters) (F : Family) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : Rows P F (fun q => residueBits (x q))) : IntegralMixedValueRowModel.Matches P F (fun q => residueBits (patch P F x q)) := by
  intro q hv hr hlo hhi
  dsimp only
  by_cases hc : IntegralMixedVirtualContextBits.context P q
  · rw [patch_good P F x q hc]
    exact hm q hv hr hlo hhi hc
  · have hn : IntegralMixedRoutineTaskBits.routine P q ≠ 3 := by omega
    simp only [patch, ite_eq_right hc, ite_eq_right hn, ite_eq_left hr]
    exact (Classical.choose_spec (IntegralMixedValueRowModel.canonical P F q)).trans
      (IntegralMixedValueRowModel.value_matches P F q hv hr hlo hhi)
end LeanCanny.Algebra.IntegralMixedGramScopedBits
