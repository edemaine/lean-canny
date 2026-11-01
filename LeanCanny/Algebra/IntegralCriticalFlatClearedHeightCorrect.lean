/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatClearedHeight
public import LeanCanny.Algebra.IntegralCriticalFlatCreatingFP
public import LeanCanny.Algebra.IntegralCriticalHeightValue

/-! # The phase-two result is the actual original source height entry

On a creating task the whole source family is transported from stateAt to
its exact deterministic birth source. Empty and invalid births use zero;
no artificial fallback polynomial or retained-height evaluator is supplied.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatClearedHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalScript IntegralCriticalFlatHeightBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] CommonHeightBits.finish CommonHeightBits.Source.rawValue CommonHeightBits.Source.value
  State.clearedEntry IntegralHistoryCriticalBits.heightValue

noncomputable def clearedBankValue (F : Scripts) (r : List Bool) (j : ℕ) (select : ℕ → ℕ)
    (i row col modulus : ℕ) : List Bool :=
  (stateAt (F.rules r) (F.length_le r) (F.scalar_bound r) j).clearedEntry select i row col modulus

theorem sourceValue_bank (F : Scripts) (q : List Bool) :
    (source F).value q = clearedBankValue F (root q) (length F q) (selector F q)
      (coordinate F q) (row F q) (col F q) (IntegralCriticalHistoryTask.modulus F.toParameters q) :=
  IntegralCriticalScriptHeightBits.sourceValue_clearedEntry (queries F) q

theorem sourceValue_original_height (F : Scripts) (q : List Bool)
    (h : IntegralCriticalHistoryTask.birth F.toParameters q < (F.rules (root q)).length) :
    (source F).value q = IntegralHistoryCriticalBits.heightValue (creatingFamily F q h)
      (coordinate F q) (row F q) (col F q) (IntegralCriticalHistoryTask.modulus F.toParameters q) := by
  let G := generatorQueries F (fun _ => q) (fun _ => h)
  have HG : (older (G.rules q) (G.selected q)).length = IntegralCriticalHistoryTask.birth F.toParameters q :=
    creating_older_length F q h
  have HL : length F q = IntegralCriticalHistoryTask.birth F.toParameters q :=
    (past_length _ _).trans (min_eq_left h.le)
  have HS : IntegralCriticalScriptDenominatorFP.selector G q = selector F q := by
    funext i
    unfold IntegralCriticalScriptDenominatorFP.selector selector
    rw [HG]
    unfold IntegralCriticalScriptFP.selector IntegralCriticalScriptFP.commandAt
    dsimp only [IntegralCriticalFlatCompanionBits.metadata, metadata, G, generatorQueries]
    cases (F.rules (root q)).reverse[IntegralCriticalHistoryTask.birth F.toParameters q]? <;> rfl
  have HE := IntegralCriticalScriptDenominatorFP.heightValue_entry G q (coordinate F q) (row F q) (col F q)
    (IntegralCriticalHistoryTask.modulus F.toParameters q)
  have HB : clearedBankValue F (root q) (older (G.rules q) (G.selected q)).length
      (IntegralCriticalScriptDenominatorFP.selector G q) (coordinate F q) (row F q) (col F q)
      (IntegralCriticalHistoryTask.modulus F.toParameters q) =
      IntegralHistoryCriticalBits.heightValue (IntegralCriticalScriptDenominatorFP.atSource G q)
        (coordinate F q) (row F q) (col F q) (IntegralCriticalHistoryTask.modulus F.toParameters q) := HE
  rw [sourceValue_bank]
  calc
    _ = clearedBankValue F (root q) (older (G.rules q) (G.selected q)).length
        (IntegralCriticalScriptDenominatorFP.selector G q) (coordinate F q) (row F q) (col F q)
        (IntegralCriticalHistoryTask.modulus F.toParameters q) := by rw [HG, HL, HS]
    _ = _ := HB.trans (congrArg (fun V => IntegralHistoryCriticalBits.heightValue V
      (coordinate F q) (row F q) (col F q) (IntegralCriticalHistoryTask.modulus F.toParameters q))
      ((IntegralCriticalScriptDenominatorFP.atSource_eq G q).trans (generator_birthSource F (fun _ => q) (fun _ => h) q)))

theorem program_original_height (F : Scripts) (answer : List Bool → List Bool)
    (ha : ∀ q, request F (rawTask F q) → answer (earlierChild F q) = companionValue F (earlierChild F q))
    (q : List Bool) (h : IntegralCriticalHistoryTask.birth F.toParameters q < (F.rules (root q)).length) :
    (program F).value answer q = IntegralHistoryCriticalBits.heightValue (creatingFamily F q h)
      (coordinate F q) (row F q) (col F q) (IntegralCriticalHistoryTask.modulus F.toParameters q) :=
  (program_value F answer ha q).trans (sourceValue_original_height F q h)

theorem missing_request (F : Scripts) (q : List Bool)
    (h : ¬ IntegralCriticalHistoryTask.birth F.toParameters q < (F.rules (root q)).length) :
    ¬ request F (rawTask F q) := by
  have HC : IntegralCriticalScriptFP.commandAt (metadata F) q (IntegralCriticalHistoryTask.birth F.toParameters q) = none :=
    IntegralCriticalScriptFP.commandAt_none _ _ _ (by exact Nat.le_of_not_gt h)
  have HS : selected F q = IntegralCriticalHistoryTask.birth F.toParameters q := by
    unfold selected selector IntegralCriticalScriptFP.selector
    rw [HC]
  intro hr
  have HV := (rawTask_valid F q).mp hr.1
  rw [HS] at HV
  exact (not_lt_of_ge (length_le_birth F q)) HV

theorem outside_request (F : Scripts) (q : List Bool) (h : ¬ coordinate F q < F.ambient (root q) + 1) :
    ¬ request F (rawTask F q) := by
  intro hr
  have HV := (rawTask_valid F q).mp hr.1
  unfold selected at HV
  rw [selector_outside F q (coordinate F q) h] at HV
  exact (not_lt_of_ge (length_le_birth F q)) HV

theorem missing_value (F : Scripts) (answer : List Bool → List Bool) (q : List Bool)
    (h : ¬ IntegralCriticalHistoryTask.birth F.toParameters q < (F.rules (root q)).length) :
    (program F).value answer q = [] := by
  have HR : (program F).request q = false := by
    change decide (request F (rawTask F q)) = false
    exact decide_eq_false (missing_request F q h)
  unfold SingleCall.Program.value
  rw [HR]
  rfl

end LeanCanny.Algebra.IntegralCriticalFlatClearedHeightBits
