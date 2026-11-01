/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalCreatingRetarget
public import LeanCanny.Algebra.IntegralCriticalTotalCoefficientValue
/-! # One total actual creating source over all flat task words

An invalid chronological birth selects one fixed base integer algebra.
Valid tasks retain the exact original prefix, bank, basis, and polynomial.
Only query fields are decoded from the current task.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalScriptQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

theorem value_coefficientEntry (F : Families) (q : Queries F) (c : List Bool) :
    (source F q).value c = residueBits (IntegralHistoryCriticalBits.coefficientEntry (F c)
      (q.coefficientIndex c) (q.row c).val (q.col c).val (q.modulus c)) := by
  have HR : (q.row c).val < (IntegralHistoryCriticalBits.source (F c)).rank [] := (q.row c).isLt
  have HT : (q.col c).val < (IntegralHistoryCriticalBits.source (F c)).rank [] := (q.col c).isLt
  rw [value]
  unfold IntegralHistoryCriticalBits.coefficientEntry
  dsimp only
  simp only [Nat.mod_eq_of_lt HR, Nat.mod_eq_of_lt HT]
  rfl
end LeanCanny.Algebra.IntegralCriticalScriptQueryBits

namespace LeanCanny.Algebra.IntegralCriticalTotalCreatingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalScript IntegralCriticalTotalCompanionBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def dummyCommand : Command 0 2 2 0 where
  low := 0
  leading := 1
  degree := 2
  degree_two := by decide
  degree_le := by decide
  degree_lt := by decide
  low_degree := by simp
  leading_ne := by decide
  low_height _ := by simp
  leading_height := by decide
  offset := 0
  objective := 0
  coordinate := 0
  selected _ := 0

noncomputable def dummy : IntegralHistoryCriticalBits.Family :=
  IntegralCriticalScript.family (base 0 0 0 2 2 0) (by decide) dummyCommand

noncomputable def atFamily (F : Scripts) (q : List Bool) : IntegralHistoryCriticalBits.Family :=
  if h : valid F q then IntegralCriticalFlatHeightBits.creatingFamily F q h else dummy

theorem atFamily_valid (F : Scripts) (q : List Bool) (h : valid F q) :
    atFamily F q = IntegralCriticalFlatHeightBits.creatingFamily F q h := dite_eq_left h

theorem atFamily_invalid (F : Scripts) (q : List Bool) (h : ¬ valid F q) : atFamily F q = dummy := dite_eq_right h

theorem atFamily_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c) :
    atFamily F q = atFamily F c := by
  have HV : valid F q ↔ valid F c := by change _ < (F.rules (root q)).length ↔ _; rw [hr, hb]
  by_cases h : valid F q
  · rw [atFamily_valid F q h, atFamily_valid F c (HV.mp h)]
    exact creator_invariance F q c h (HV.mp h) hr hb
  · rw [atFamily_invalid F q h, atFamily_invalid F c (fun hc => h (HV.mpr hc))]

noncomputable def rank (F : Scripts) (q : List Bool) : ℕ := count ((atFamily F q).birth []) ((atFamily F q).width [])
theorem rank_pos (F : Scripts) (q : List Bool) : 0 < rank F q := pow_pos (Nat.two_pow_pos _) _

noncomputable def queries (F : Scripts) : IntegralCriticalScriptQueryBits.Queries (atFamily F) where
  coefficientIndex := IntegralCriticalHistoryTask.get F.toParameters .coefficient
  target := IntegralCriticalHistoryTask.get F.toParameters .target
  row q := ⟨IntegralCriticalHistoryTask.get F.toParameters .row q % rank F q, Nat.mod_lt _ (rank_pos F q)⟩
  col q := ⟨IntegralCriticalHistoryTask.get F.toParameters .col q % rank F q, Nat.mod_lt _ (rank_pos F q)⟩
  modulus := IntegralCriticalHistoryTask.modulus F.toParameters
  modulus_ne_zero := IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters

noncomputable def family (F : Scripts) := IntegralCriticalScriptQueryBits.family (atFamily F) (queries F)
noncomputable def source (F : Scripts) := IntegralHistoryCriticalBits.source (family F)
noncomputable def euler (F : Scripts) := (source F).toEuler

noncomputable def coefficientValue (F : Scripts) (q : List Bool) : List Bool :=
  if valid F q then (source F).value q else []

theorem coefficientValue_invalid (F : Scripts) (q : List Bool) (h : ¬ valid F q) : coefficientValue F q = [] := ite_eq_right h

attribute [local irreducible] IntegralHistoryCriticalBits.coefficientEntry

theorem coefficientValue_valid (F : Scripts) (q : List Bool) (h : valid F q) :
    coefficientValue F q = IntegralCriticalTotalCompanionBits.coefficientValue F q := by
  unfold coefficientValue
  rw [ite_eq_left h, IntegralCriticalTotalCompanionBits.coefficientValue, coefficientAt_creating F q h]
  change (IntegralCriticalScriptQueryBits.source (atFamily F) (queries F)).value q = _
  rw [IntegralCriticalScriptQueryBits.value_coefficientEntry]
  change residueBits (IntegralHistoryCriticalBits.coefficientEntry (atFamily F q)
    (IntegralCriticalHistoryTask.get F.toParameters .coefficient q)
    (IntegralCriticalHistoryTask.get F.toParameters .row q % rank F q)
    (IntegralCriticalHistoryTask.get F.toParameters .col q % rank F q)
    (IntegralCriticalHistoryTask.modulus F.toParameters q)) = _
  have HR : rank F q = (IntegralHistoryCriticalBits.source (atFamily F q)).rank [] := rfl
  rw [HR, IntegralHistoryCriticalBits.coefficientEntry_mod, atFamily_valid F q h]
theorem coefficientValue_eq (F : Scripts) (q : List Bool) :
    coefficientValue F q = IntegralCriticalTotalCompanionBits.coefficientValue F q := by
  by_cases h : valid F q
  · exact coefficientValue_valid F q h
  · rw [coefficientValue_invalid F q h, IntegralCriticalTotalCompanionBits.coefficientValue_invalid F q h]

end LeanCanny.Algebra.IntegralCriticalTotalCreatingBits
