/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscUpperOutside
public import LeanCanny.Algebra.IntegralMixedPscNativeFactor
/-! # Literal components of the native PSC determinant routine -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscUpperModel
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedPscUpperBits
open scoped Classical

noncomputable def component (P : Parameters) (F : Family) (p : ℕ) (q : List Bool) : List Bool :=
  if p = 0 then IntegralMixedPscActionBits.value P F q else
  if p = 1 then entryValue P F q else
  if p = 2 then momentValue P F q else
  if p = 3 then factorValue P F q else
  if p = 4 then characteristicValue P F q else []

noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  if selected P F .originalCoefficient q then IntegralMixedPscActionBits.value P F q else
  if decide (Selected1 P F q) then entryValue P F q else
  if selected P F .clearedHeight q then momentValue P F q else
  if selected3 P F q then factorValue P F q else
  if decide (Selected4 P F q) then characteristicValue P F q else []

theorem value_phase (P : Parameters) (F : Family) (q : List Bool) (p : ℕ)
    (ha : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4)
    (hq : Domain P F q) (hp : phase q = p) :
    value P F q = component P F p q := by
  rcases ha with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [value, component, selected, selected3, Selected1, Selected4, hq, hp, isPhase, Phase.code,
    Nat.reduceEqDiff, true_and, false_and, and_false, decide_true, decide_false, Bool.false_eq_true,
    decide_eq_true_eq, Bool.true_and, Bool.false_and, ite_true, ite_false]
  · split
    · rfl
    · exact (entry_outside P F q (by assumption)).symm
  · split
    · rfl
    · exact (factor_outside P F q (by assumption)).symm
  · split
    · rfl
    · exact (characteristic_outside P F q (by assumption)).symm

theorem canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = value P F q := by
  unfold value
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · rw [moment_snapshot]
    exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  · exact ⟨0, by simp only [residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]⟩

abbrev Matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, Domain P F q → (phase q = 0 ∨ phase q = 1 ∨ phase q = 2 ∨ phase q = 3 ∨ phase q = 4) →
    answer q = component P F (phase q) q

theorem value_matches (P : Parameters) (F : Family) : Matches P F (value P F) := by
  intro q hq hp
  exact value_phase P F q (phase q) hp hq rfl

end LeanCanny.Algebra.IntegralMixedPscUpperModel
