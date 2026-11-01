/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCompanionAccess
/-! # Creating sources depend only on root and chronological birth -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalScript IntegralCriticalFlatHeightBits
set_option backward.isDefEq.respectTransparency false

theorem creator_invariance (F : Scripts) (q c : List Bool) (hq : valid F q) (hc : valid F c)
    (hr : root q = root c) (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c) :
    creatingFamily F q hq = creatingFamily F c hc :=
  creatingAt_congr F _ _ _ _ hq hc hr hb

theorem coefficient_invalid (F : Scripts) (q : List Bool) (h : ¬ valid F q) (k : ℕ) : coefficient F q k = 0 := by
  ext r t
  unfold coefficient
  split_ifs with hk
  · change (leading F q) * (1 : Matrix _ _ _) r t = 0
    unfold leading leadingInteger
    rw [dite_eq_right h, Int.cast_zero, zero_mul]
  · rfl

theorem coefficientAt_invalid (F : Scripts) (q : List Bool) (h : ¬ valid F q) (k r t : ℕ) : coefficientAt F q k r t = [] := by
  unfold coefficientAt
  rw [coefficient_invalid F q h k]
  simp [residueBits, BinaryNatCode.encode]
end LeanCanny.Algebra.IntegralCriticalTotalCompanionBits
