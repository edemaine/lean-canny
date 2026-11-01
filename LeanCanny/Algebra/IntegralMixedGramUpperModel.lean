/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramUpperOutside
/-! # Literal components of the native Gram determinant routine -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramUpperModel
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedGramUpperBits
open scoped Classical

noncomputable def component (P : Parameters) (F : Family) (p : ℕ) (q : List Bool) : List Bool :=
  if p = 19 then IntegralMixedGramBlockEntryNative.value P F q else
  if p = 21 then entryValue P F q else
  if p = 22 then momentValue P F q else
  if p = 23 then IntegralMixedGramMatrixModel.factorValue P F q else
  if p = 24 then characteristicValue P F q else []

noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  if selected P .actionEntry q then IntegralMixedGramBlockEntryNative.value P F q else
  if decide (Selected21 P F q) then entryValue P F q else
  if selected P .momentPower q then momentValue P F q else
  if selectedFinite P .relativeFactor (factorSize P F) q then IntegralMixedGramMatrixModel.factorValue P F q else
  if selectedFinite P .relativePower (fun q => (characteristic P F).rank q) q then characteristicValue P F q else []

theorem value_phase (P : Parameters) (F : Family) (q : List Bool) (p : ℕ)
    (ha : p = 19 ∨ p = 21 ∨ p = 22 ∨ p = 23 ∨ p = 24)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 3) (hp : phase q = p) :
    value P F q = component P F p q := by
  rcases ha with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [value, component, selected, selectedFinite, Selected21, hv, hr, hp, isPhase, Phase.code,
    Nat.reduceEqDiff, true_and, false_and, and_false, decide_true, decide_false, Bool.false_eq_true,
    decide_eq_true_eq, ite_true, ite_false]
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
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 3 →
    (phase q = 19 ∨ phase q = 21 ∨ phase q = 22 ∨ phase q = 23 ∨ phase q = 24) →
      answer q = component P F (phase q) q

theorem value_matches (P : Parameters) (F : Family) : Matches P F (value P F) := by
  intro q hv hr hp
  exact value_phase P F q (phase q) hp hv hr rfl

end LeanCanny.Algebra.IntegralMixedGramUpperModel
