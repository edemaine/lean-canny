/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalTotalCompanionAccess
public import LeanCanny.Algebra.IntegralCriticalFlatCompanion

/-! # Total phase-26 companion control over root scripts

The valid-birth guard suppresses the scalar shift branch for missing
commands. Every nonlocal entry requests one phase-25 coefficient in the
same root and birth, with normalized old-basis indices.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def child (F : Scripts) (q : List Bool) : List Bool :=
  IntegralCriticalFlatCompanionBits.writer F.toParameters (IntegralScalarGeneratorBits.coefficientQuery (family F) q)

attribute [local irreducible] IntegralScalarGeneratorBits.finish IntegralScalarGeneratorBits.immediate IntegralScalarGeneratorBits.request

noncomputable def program (F : Scripts) : SingleCall.Program where
  request q := decide (valid F q ∧ IntegralScalarGeneratorBits.request (family F) q)
  query := child F
  immediate q := if valid F q then IntegralScalarGeneratorBits.immediate (family F) q else []
  finish := IntegralScalarGeneratorBits.finish (family F)

theorem child_FP (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) : child F ∈ FP :=
  mem_FP_comp (IntegralScalarGeneratorBits.coefficientQuery_FP (family F) (access F a n))
    (IntegralCriticalFlatCompanionBits.writer_FP _ a.toAccess)

theorem program_controls (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)) : (program F).Controls := by
  constructor
  · change (fun q => [decide (valid F q ∧ IntegralScalarGeneratorBits.request (family F) q)]) ∈ FP
    exact ((valid_FP F a).and (IntegralScalarGeneratorBits.request_FP (family F) (access F a n))).flag_mem_FP
  · change child F ∈ FP
    exact child_FP F a n
  · change (fun q => if valid F q then IntegralScalarGeneratorBits.immediate (family F) q else []) ∈ FP
    exact (valid_FP F a).ite_mem_FP (IntegralScalarGeneratorBits.immediate_FP (family F) (access F a n)) (constFn_mem_FP [])
  · change IntegralScalarGeneratorBits.finish (family F) ∈ FP
    exact IntegralScalarGeneratorBits.finish_FP (family F) (access F a n) (leading_FP F a n)

theorem missing_value (F : Scripts) (answer : List Bool → List Bool) (q : List Bool) (h : ¬ valid F q) :
    (program F).value answer q = [] := by
  have HR : (program F).request q = false := by
    change decide (valid F q ∧ IntegralScalarGeneratorBits.request (family F) q) = false
    exact decide_eq_false (fun hr => h hr.1)
  unfold SingleCall.Program.value
  rw [HR]
  change (if valid F q then _ else []) = []
  exact ite_eq_right h

theorem valid_value (F : Scripts) (answer : List Bool → List Bool) (q : List Bool) (h : valid F q) :
    (program F).value answer q =
      (IntegralScalarGeneratorBits.program (family F) (IntegralCriticalFlatCompanionBits.writer F.toParameters)).value answer q := by
  unfold SingleCall.Program.value program IntegralScalarGeneratorBits.program
  simp only [h, true_and, ite_true]
  rfl

theorem requests_iff (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool) :
    (program F).controller.Requests answer budget q c ↔
      valid F q ∧ IntegralScalarGeneratorBits.request (family F) q ∧ c = child F q := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq, and_assoc]

theorem child_root (F : Scripts) (q : List Bool) : root (child F q) = root q := by
  change RankedHistoryTask.root (child F q) = RankedHistoryTask.root q
  unfold child
  rw [IntegralCriticalFlatCompanionBits.writer_root]
  simp only [IntegralScalarGeneratorBits.coefficientQuery, pairFst_pair]

theorem child_birth (F : Scripts) (q : List Bool) :
    IntegralCriticalHistoryTask.birth F.toParameters (child F q) = IntegralCriticalHistoryTask.birth F.toParameters q := by
  unfold child
  rw [IntegralCriticalFlatCompanionBits.writer_birth]
  simp only [IntegralScalarGeneratorBits.coefficientQuery, pairFst_pair]

theorem child_phase (F : Scripts) (q : List Bool) :
    IntegralCriticalHistoryTask.phase (child F q) = IntegralCriticalHistoryTask.Phase.criticalCoefficient.code :=
  IntegralCriticalFlatCompanionBits.writer_phase _ _

theorem child_rank (F : Scripts) (q : List Bool) (hp : IntegralCriticalHistoryTask.isPhase .companion q) :
    IntegralCriticalHistoryTask.rank F.toParameters (child F q) < IntegralCriticalHistoryTask.rank F.toParameters q := by
  have H := IntegralCriticalFlatCompanionBits.writer_lower_rank F.toParameters
    (IntegralScalarGeneratorBits.coefficientQuery (family F) q) (by
      simpa only [IntegralScalarGeneratorBits.coefficientQuery, pairFst_pair] using hp)
  simpa only [child, IntegralScalarGeneratorBits.coefficientQuery, pairFst_pair] using H

theorem child_length (F : Scripts) (q : List Bool) : (child F q).length ≤ IntegralCriticalHistoryTask.wordBudget F.toParameters q := by
  unfold child IntegralCriticalFlatCompanionBits.writer
  have H := IntegralCriticalHistoryTask.child_length F.toParameters pairFst
    (IntegralCriticalHistoryTask.birth F.toParameters ∘ pairFst) .criticalCoefficient
    (IntegralCriticalFlatCompanionBits.reader F.toParameters)
    (IntegralScalarGeneratorBits.coefficientQuery (family F) q) (min_le_right _ _)
  simpa only [IntegralScalarGeneratorBits.coefficientQuery, pairFst_pair] using H

end LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
