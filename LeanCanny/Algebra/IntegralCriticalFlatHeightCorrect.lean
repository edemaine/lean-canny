/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatHeight
public import LeanCanny.Algebra.IntegralCriticalStateEntry

/-! # Actual value correctness of the flat retained-height child

The one recursive answer is the creating companion, in its actual birth
basis. No retained numerator evaluator is supplied as a local control.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial UniformIntegralPrefix
open IntegralCriticalScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def selected (F : Scripts) (q : List Bool) (h : valid F q) :
    Fin (past (F.rules (root q)) (length F q)).length :=
  ⟨IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q, by
    rw [past_length, min_eq_left (length_le_full F q)]
    exact h⟩

noncomputable def selectedFamily (F : Scripts) (q : List Bool) (h : valid F q) :=
  birthFamily (past (F.rules (root q)) (length F q))
    (past_bound _ (F.length_le (root q)) _) (F.scalar_bound (root q)) (selected F q h)

theorem rawValue_valid (F : Scripts) (q : List Bool) (h : valid F q) :
    rawValue F q = if row F q % radix F q = col F q % radix F q then
      IntegralCriticalCreatingBits.value (selectedFamily F q h)
        (row F q / radix F q) (col F q / radix F q) (IntegralCriticalHistoryTask.modulus F.toParameters q) else [] := by
  have HL : (past (F.rules (root q)) (length F q)).length = length F q :=
    (past_length _ _).trans (min_eq_left (length_le_full F q))
  have HS : IntegralCriticalScriptHeightBits.select (heightQueries F) q 0 = some (selected F q h) := by
    unfold IntegralCriticalScriptHeightBits.select
    dsimp only [heightQueries]
    have HV : IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q <
        (past (F.rules (root q)) (length F q)).length := by
      rw [HL]
      exact h
    rw [dite_eq_left HV]
    rfl
  have H := run_entry
    (past (F.rules (root q)) (length F q)) (past_bound _ (F.length_le (root q)) _)
    (F.scalar_bound (root q)) (selected F q h) ((heightQueries F).row q) ((heightQueries F).col q)
    (IntegralCriticalHistoryTask.modulus F.toParameters q)
  unfold rawValue
  rw [IntegralCriticalScriptHeightBits.rawValue_entry _ q (Nat.succ_pos _)]
  change (run (S := F.cap (root q)) (B := F.width (root q))
    (past (F.rules (root q)) (length F q)) (past_bound _ (F.length_le (root q)) _) (F.scalar_bound (root q))).entry
    (IntegralCriticalScriptHeightBits.select (heightQueries F) q 0) ((heightQueries F).row q) ((heightQueries F).col q)
    (IntegralCriticalHistoryTask.modulus F.toParameters q) = _
  rw [HS]
  simpa only [radix, index, min_eq_left h.le, selectedFamily, selected, heightQueries] using H

theorem rawValue_invalid (F : Scripts) (q : List Bool) (h : ¬ valid F q) : rawValue F q = [] := by
  have HL : (past (F.rules (root q)) (length F q)).length = length F q :=
    (past_length _ _).trans (min_eq_left (length_le_full F q))
  have HS : IntegralCriticalScriptHeightBits.select (heightQueries F) q 0 = none := by
    unfold IntegralCriticalScriptHeightBits.select
    dsimp only [heightQueries]
    have HV : ¬ IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q <
        (past (F.rules (root q)) (length F q)).length := by
      rw [HL]
      exact h
    rw [dite_eq_right HV]
  unfold rawValue
  rw [IntegralCriticalScriptHeightBits.rawValue_entry _ q (Nat.succ_pos _)]
  have HC : (heightQueries F).coordinate q = 0 := rfl
  rw [HC, HS, State.entry_none]

theorem child_creating_valid (F : Scripts) (q : List Bool) (h : valid F q) :
    IntegralCriticalHistoryTask.birth F.toParameters (child F q) < (F.rules (root (child F q))).length := by
  rw [child_birth, child_root]
  have HL := length_le_full F q
  unfold childBirth
  unfold valid at h
  omega

theorem creatingAt_congr (F : Scripts) (r s : List Bool) (j k : ℕ)
    (hj : j < (F.rules r).length) (hk : k < (F.rules s).length) (hr : r = s) (hb : j = k) :
    creatingAt F r j hj = creatingAt F s k hk := by
  subst s
  subst k
  rfl

theorem child_creatingFamily (F : Scripts) (q : List Bool) (h : valid F q) :
    creatingFamily F (child F q) (child_creating_valid F q h) = selectedFamily F q h := by
  unfold selectedFamily
  conv_rhs => rw [birthFamily_past (F.rules (root q)) (F.length_le (root q))
    (F.scalar_bound (root q)) (length F q) (length_le_full F q) (selected F q h)]
  unfold creatingFamily
  have HV : childBirth F q < (F.rules (root q)).length := by
    have HL := length_le_full F q
    unfold valid at h
    unfold childBirth
    omega
  refine (creatingAt_congr F _ _ _ _ (child_creating_valid F q h) HV (child_root F q) (child_birth F q)).trans ?_
  unfold creatingAt
  congr 1
  apply Fin.ext
  simp only [pastIndex, selected]
  have HI : index F q = IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q := min_eq_left h.le
  have HL := length_le_full F q
  unfold childBirth
  unfold valid at h
  omega

theorem companion_child (F : Scripts) (q : List Bool) (h : valid F q) :
    companionValue F (child F q) = IntegralCriticalCreatingBits.value (selectedFamily F q h)
      (row F q / radix F q) (col F q / radix F q) (IntegralCriticalHistoryTask.modulus F.toParameters q) := by
  unfold companionValue
  rw [dite_eq_left (child_creating_valid F q h), child_creatingFamily F q h, child_row, child_col, child_modulus]

noncomputable def program (F : Scripts) : SingleCall.Program where
  request q := decide (request F q)
  query := child F
  immediate _ := []
  finish := pairSnd

theorem program_controls (F : Scripts) (a : Access F) : (program F).Controls :=
  ⟨(request_FP F a).flag_mem_FP, child_FP F a, constFn_mem_FP [], pairSnd_mem_FP⟩

theorem program_value (F : Scripts) (answer : List Bool → List Bool)
    (ha : ∀ q, request F q → answer (child F q) = companionValue F (child F q)) (q : List Bool) :
    (program F).value answer q = rawValue F q := by
  by_cases hv : valid F q
  · rw [rawValue_valid F q hv]
    by_cases hm : row F q % radix F q = col F q % radix F q
    · simp only [SingleCall.Program.value, program, request, hv, hm, and_self, decide_true, ite_true, pairSnd_pair]
      exact (ha q ⟨hv, hm⟩).trans (companion_child F q hv)
    · simp only [SingleCall.Program.value, program, request, hm, and_false, decide_false, Bool.false_eq_true, ite_false]
  · rw [rawValue_invalid F q hv]
    simp only [SingleCall.Program.value, program, request, hv, false_and, decide_false, Bool.false_eq_true, ite_false]

theorem requests_iff (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool) :
    (program F).controller.Requests answer budget q c ↔ request F q ∧ c = child F q := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

theorem requests_rank (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (h : (program F).controller.Requests answer budget q c) :
    IntegralCriticalHistoryTask.rank F.toParameters c < IntegralCriticalHistoryTask.rank F.toParameters q := by
  obtain ⟨hr, rfl⟩ := (requests_iff F answer budget q c).mp h
  exact child_rank F q hr.1

theorem requests_length (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (h : (program F).controller.Requests answer budget q c) : c.length ≤ IntegralCriticalHistoryTask.wordBudget F.toParameters q := by
  obtain ⟨_, rfl⟩ := (requests_iff F answer budget q c).mp h
  exact child_length F q

end LeanCanny.Algebra.IntegralCriticalFlatHeightBits
