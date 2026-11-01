/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueGramSumNative
public import LeanCanny.Computation.NativeSingleCallBranch

/-! # Literal routine-two value-row and Gram components -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueRowModel
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualCaps
open scoped Classical

noncomputable def selected (P : Parameters) (p : ℕ) (q : List Bool) : Bool :=
  decide (valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 2 ∧ phase q = p)

noncomputable def component (P : Parameters) (F : Family) (p : ℕ) (q : List Bool) : List Bool :=
  if p = 21 then IntegralMixedValueRestoredSource.value P F q else
  if p = 22 then IntegralMixedValueHomogeneousMatrix.value P F q else
  if p = 23 then IntegralMixedValueReciprocalMatrix.value P F q else
  if p = 24 then IntegralMixedValueMacaulayMatrix.value P F q else
  if p = 25 then IntegralMixedValueGramProductNative.value P F q else
  if p = 26 then IntegralMixedValueGramSumSource.value P F q else []

noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  if selected P 21 q then IntegralMixedValueRestoredSource.value P F q else
  if selected P 22 q then IntegralMixedValueHomogeneousMatrix.value P F q else
  if selected P 23 q then IntegralMixedValueReciprocalMatrix.value P F q else
  if selected P 24 q then IntegralMixedValueMacaulayMatrix.value P F q else
  if selected P 25 q then IntegralMixedValueGramProductNative.value P F q else
  if selected P 26 q then IntegralMixedValueGramSumSource.value P F q else []

theorem value_phase (P : Parameters) (F : Family) (p : ℕ) (q : List Bool)
    (hlo : 21 ≤ p) (hhi : p ≤ 26) (hv : valid P q)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2) (hp : phase q = p) :
    value P F q = component P F p q := by
  have H : p = 21 ∨ p = 22 ∨ p = 23 ∨ p = 24 ∨ p = 25 ∨ p = 26 := by omega
  rcases H with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [value, selected, hv, hr, hp, component, Nat.reduceEqDiff, decide_true, decide_false,
      Bool.false_eq_true, ite_true, ite_false, true_and]

theorem value_outside (P : Parameters) (F : Family) (q : List Bool)
    (h : ¬valid P q ∨ IntegralMixedRoutineTaskBits.routine P q ≠ 2 ∨ phase q < 21 ∨ 26 < phase q) :
    value P F q = [] := by
  have H (p : ℕ) (hlo : 21 ≤ p) (hhi : p ≤ 26) : selected P p q = false := by
    rw [selected, decide_eq_false_iff_not]
    intro HS
    rcases h with hv | hr | hp | hp
    · exact hv HS.1
    · exact hr HS.2.1
    · omega
    · omega
  simp only [value, H 21 (by decide) (by decide), H 22 (by decide) (by decide),
    H 23 (by decide) (by decide), H 24 (by decide) (by decide), H 25 (by decide) (by decide),
    H 26 (by decide) (by decide), Bool.false_eq_true, ite_false]

theorem canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = value P F q := by
  unfold value
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  · exact ⟨0, by simp only [residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]⟩

abbrev Matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, valid P q → IntegralMixedRoutineTaskBits.routine P q = 2 →
    21 ≤ phase q → phase q ≤ 26 → answer q = component P F (phase q) q

theorem value_matches (P : Parameters) (F : Family) : Matches P F (value P F) := by
  intro q hv hr hlo hhi
  exact value_phase P F (phase q) q hlo hhi hv hr rfl

end LeanCanny.Algebra.IntegralMixedValueRowModel
