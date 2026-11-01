/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalHeightValue
public import LeanCanny.Algebra.IntegralCriticalSelectedHeight
public import LeanCanny.Algebra.IntegralCriticalFlatClearedHeightCorrect
/-! # The actual total height controller requests only earlier companions -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial UniformIntegralPrefix
open IntegralCriticalScript IntegralCriticalTotalCompanionBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] IntegralHistoryCriticalBits.heightValue State.clearedEntry
  CommonHeightBits.Source.value

theorem sourceValue_creating (F : Scripts) (q : List Bool) (h : valid F q) :
    (IntegralCriticalFlatClearedHeightBits.source F).value q =
      IntegralHistoryCriticalBits.heightValue (IntegralCriticalFlatHeightBits.creatingFamily F q h)
        (IntegralCriticalFlatClearedHeightBits.coordinate F q)
        (IntegralCriticalFlatHeightBits.row F q) (IntegralCriticalFlatHeightBits.col F q)
        (IntegralCriticalHistoryTask.modulus F.toParameters q) := by
  have HL : IntegralCriticalFlatHeightBits.length F q = IntegralCriticalHistoryTask.birth F.toParameters q :=
    (past_length _ _).trans (min_eq_left h.le)
  have HM : (past (F.rules (root q)) (IntegralCriticalFlatHeightBits.length F q)).length ≤ F.cap (root q) := by
    rw [past_length]
    have HB := F.length_le (root q)
    exact (min_le_left _ _).trans (by omega)
  rw [IntegralCriticalFlatClearedHeightBits.sourceValue_bank]
  have HE := State.clearedEntry_family
    (stateAt (F.rules (root q)) (F.length_le (root q)) (F.scalar_bound (root q))
      (IntegralCriticalFlatHeightBits.length F q)) HM
    (chosen (F.rules (root q)) (IntegralCriticalFlatHeightBits.creatingIndex F q h))
    (IntegralCriticalFlatClearedHeightBits.selector F q) (selector_creating F q h)
    (IntegralCriticalFlatClearedHeightBits.coordinate F q)
    (IntegralCriticalFlatHeightBits.row F q) (IntegralCriticalFlatHeightBits.col F q)
    (IntegralCriticalHistoryTask.modulus F.toParameters q)
  exact HE.trans (congrArg (fun A => IntegralHistoryCriticalBits.heightValue A
    (IntegralCriticalFlatClearedHeightBits.coordinate F q)
    (IntegralCriticalFlatHeightBits.row F q) (IntegralCriticalFlatHeightBits.col F q)
    (IntegralCriticalHistoryTask.modulus F.toParameters q)) (prefix_family F q h HM))

theorem sourceValue_valid (F : Scripts) (q : List Bool) (h : valid F q) :
    (IntegralCriticalFlatClearedHeightBits.source F).value q = value F q := by
  rw [sourceValue_creating F q h]
  unfold value entry
  rw [IntegralCriticalTotalCreatingBits.atFamily_valid F q h]
  have HD : count ((IntegralCriticalFlatHeightBits.creatingFamily F q h).birth [])
      ((IntegralCriticalFlatHeightBits.creatingFamily F q h).width []) = IntegralCriticalFlatHeightBits.dimension F q := by
    change count _ (F.width (root q)) = count _ (F.width (root q))
    rw [creating_birth]
    congr 1
    exact ((past_length _ _).trans (min_eq_left h.le)).symm
  change IntegralHistoryCriticalBits.heightValue _ _
    (IntegralCriticalHistoryTask.get F.toParameters .row q % IntegralCriticalFlatHeightBits.dimension F q)
    (IntegralCriticalHistoryTask.get F.toParameters .col q % IntegralCriticalFlatHeightBits.dimension F q) _ = _
  rw [← HD]
  exact IntegralHistoryCriticalBits.heightValue_mod _ _ _ _ _

noncomputable abbrev program := IntegralCriticalFlatClearedHeightBits.program

theorem program_value (F : Scripts) (answer : List Bool → List Bool)
    (ha : ∀ q, IntegralCriticalFlatHeightBits.request F (IntegralCriticalFlatClearedHeightBits.rawTask F q) →
      answer (IntegralCriticalFlatClearedHeightBits.earlierChild F q) =
        IntegralCriticalFlatHeightBits.companionValue F (IntegralCriticalFlatClearedHeightBits.earlierChild F q))
    (q : List Bool) : (program F).value answer q = value F q := by
  by_cases h : valid F q
  · exact (IntegralCriticalFlatClearedHeightBits.program_value F answer ha q).trans (sourceValue_valid F q h)
  · rw [IntegralCriticalFlatClearedHeightBits.missing_value F answer q h, value_invalid F q h]

theorem program_value_local (F : Scripts) (answer : List Bool → List Bool) (q : List Bool)
    (ha : IntegralCriticalFlatHeightBits.request F (IntegralCriticalFlatClearedHeightBits.rawTask F q) →
      answer (IntegralCriticalFlatClearedHeightBits.earlierChild F q) =
        IntegralCriticalFlatHeightBits.companionValue F (IntegralCriticalFlatClearedHeightBits.earlierChild F q)) :
    (program F).value answer q = value F q := by
  have HC (P : SingleCall.Program) (a b : List Bool → List Bool) (c : List Bool)
      (h : P.request c = true → a (P.query c) = b (P.query c)) : P.value a c = P.value b c := by
    unfold SingleCall.Program.value
    split_ifs with hr
    · rw [h hr]
    · rfl
  apply (HC (program F) answer (IntegralCriticalFlatHeightBits.companionValue F) q ?_).trans
    (program_value F _ (fun _ _ => rfl) q)
  intro hr
  exact ha (of_decide_eq_true hr)

theorem program_controls (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) :
    (program F).Controls := IntegralCriticalFlatClearedHeightBits.program_controls F a n

theorem requests_rank (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (h : (program F).controller.Requests answer budget q c) :
    IntegralCriticalHistoryTask.rank F.toParameters c < IntegralCriticalHistoryTask.rank F.toParameters q :=
  IntegralCriticalFlatClearedHeightBits.requests_rank F answer budget q c h

theorem requests_length (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (h : (program F).controller.Requests answer budget q c) :
    c.length ≤ IntegralCriticalHistoryTask.wordBudget F.toParameters q :=
  IntegralCriticalFlatClearedHeightBits.requests_length F answer budget q c h

theorem requests_phase (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (h : (program F).controller.Requests answer budget q c) : IntegralCriticalHistoryTask.isPhase .companion c := by
  obtain ⟨_, rfl⟩ := (IntegralCriticalFlatClearedHeightBits.requests_iff F answer budget q c).mp h
  exact IntegralCriticalFlatHeightBits.child_phase F _

theorem requests_root (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (h : (program F).controller.Requests answer budget q c) : root c = root q := by
  obtain ⟨_, rfl⟩ := (IntegralCriticalFlatClearedHeightBits.requests_iff F answer budget q c).mp h
  exact IntegralCriticalFlatClearedHeightBits.earlierChild_root F q

theorem requests_birth (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (h : (program F).controller.Requests answer budget q c) :
    IntegralCriticalHistoryTask.birth F.toParameters c < IntegralCriticalHistoryTask.birth F.toParameters q := by
  obtain ⟨hr, rfl⟩ := (IntegralCriticalFlatClearedHeightBits.requests_iff F answer budget q c).mp h
  exact IntegralCriticalFlatClearedHeightBits.earlierChild_birth_lt F q hr.1

theorem requests_valid (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (h : (program F).controller.Requests answer budget q c) : valid F c := by
  have HP : valid F q := by
    by_contra hn
    exact IntegralCriticalFlatClearedHeightBits.missing_request F q hn
      ((IntegralCriticalFlatClearedHeightBits.requests_iff F answer budget q c).mp h).1
  change IntegralCriticalHistoryTask.birth F.toParameters c < (F.rules (root c)).length
  rw [requests_root F answer budget q c h]
  exact (requests_birth F answer budget q c h).trans HP

end LeanCanny.Algebra.IntegralCriticalTotalHeightBits
