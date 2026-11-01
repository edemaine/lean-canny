/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatBankValue

/-! # One earlier companion child for actual common-cleared heights

The raw retained-height controller is inlined under the local modular
cofactor multiplication. There is no recursive same-birth raw-height task.
Missing selectors and unequal low digits return zero without a child.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatClearedHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalScript IntegralCriticalFlatHeightBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def source (F : Scripts) : CommonHeightBits.Source := IntegralCriticalScriptHeightBits.source (queries F)

attribute [local irreducible] CommonHeightBits.finish CommonHeightBits.Source.rawValue CommonHeightBits.Source.value

noncomputable def program (F : Scripts) : SingleCall.Program where
  request q := decide (request F (rawTask F q))
  query := earlierChild F
  immediate _ := []
  finish := CommonHeightBits.finish (source F)

theorem program_controls (F : Scripts) (a : Access F) (n : IntegralCriticalScriptFP.Access (metadata F)) : (program F).Controls := by
  constructor
  · change (fun q => [decide (request F (rawTask F q))]) ∈ FP
    exact mem_FP_comp (rawTask_FP F a n) (IntegralCriticalFlatHeightBits.program_controls F a).request
  · change earlierChild F ∈ FP
    exact earlierChild_FP F a n
  · change (fun _ : List Bool => ([] : List Bool)) ∈ FP
    exact constFn_mem_FP []
  · change CommonHeightBits.finish (source F) ∈ FP
    exact CommonHeightBits.finish_FP (source F) (access F a n)

theorem finish_zero (S : CommonHeightBits.Source) (q : List Bool) : CommonHeightBits.finish S (pair q []) = [] := by
  unfold CommonHeightBits.finish
  rw [pairFst_pair, pairSnd_pair]
  simp only [BinaryNat.mulMod_pair]
  rw [show Nat.fromBitsLE ([] : List Bool) = 0 from by decide, Nat.mul_zero, Nat.zero_mod]
  rfl

theorem program_value (F : Scripts) (answer : List Bool → List Bool)
    (ha : ∀ q, request F (rawTask F q) → answer (earlierChild F q) = companionValue F (earlierChild F q)) (q : List Bool) :
    (program F).value answer q = (source F).value q := by
  by_cases hr : request F (rawTask F q)
  · have HV : answer (earlierChild F q) = (source F).rawValue q := by
      have HE := ha q hr
      have HB := companion_child F (rawTask F q) hr.1
      have HRaw := rawValue_valid F (rawTask F q) hr.1
      rw [ite_eq_left hr.2] at HRaw
      exact HE.trans (HB.trans (HRaw.symm.trans (rawTask_rawValue F q)))
    have HR : (program F).request q = true := by
      change decide (request F (rawTask F q)) = true
      exact decide_eq_true hr
    calc
      _ = CommonHeightBits.finish (source F) (pair q (answer (earlierChild F q))) := by
        unfold SingleCall.Program.value
        rw [HR]
        rfl
      _ = _ := (congrArg (fun w => CommonHeightBits.finish (source F) (pair q w)) HV).trans
        (CommonHeightBits.finish_value (source F) q)
  · have HZeroRaw : rawValue F (rawTask F q) = [] := by
      by_cases hv : valid F (rawTask F q)
      · rw [rawValue_valid F (rawTask F q) hv, ite_eq_right (by
          intro hm
          exact hr ⟨hv, hm⟩)]
      · exact rawValue_invalid F (rawTask F q) hv
    have HZero : (source F).rawValue q = [] := (rawTask_rawValue F q).symm.trans HZeroRaw
    have HR : (program F).request q = false := by
      change decide (request F (rawTask F q)) = false
      exact decide_eq_false hr
    have HP : (program F).value answer q = [] := by
      unfold SingleCall.Program.value
      rw [HR]
      rfl
    exact HP.trans ((finish_zero (source F) q).symm.trans
      ((congrArg (fun w => CommonHeightBits.finish (source F) (pair q w)) HZero.symm).trans
        (CommonHeightBits.finish_value (source F) q)))

theorem requests_iff (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool) :
    (program F).controller.Requests answer budget q c ↔ request F (rawTask F q) ∧ c = earlierChild F q := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

theorem requests_rank (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (h : (program F).controller.Requests answer budget q c) :
    IntegralCriticalHistoryTask.rank F.toParameters c < IntegralCriticalHistoryTask.rank F.toParameters q := by
  obtain ⟨hr, rfl⟩ := (requests_iff F answer budget q c).mp h
  exact earlierChild_rank F q hr.1

theorem requests_length (F : Scripts) (answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (h : (program F).controller.Requests answer budget q c) : c.length ≤ IntegralCriticalHistoryTask.wordBudget F.toParameters q := by
  obtain ⟨_, rfl⟩ := (requests_iff F answer budget q c).mp h
  exact earlierChild_length F q

end LeanCanny.Algebra.IntegralCriticalFlatClearedHeightBits
