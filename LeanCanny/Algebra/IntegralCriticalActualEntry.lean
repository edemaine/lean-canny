/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualModel
public import LeanCanny.Algebra.IntegralCriticalTotalCompanionInvariant
/-! # Phase refresh retains the actual creating generator entry -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalCreatingBits.value IntegralCriticalFlatHeightBits.creatingFamily

theorem valid_next (F : Scripts) (p : Phase) (q : List Bool) :
    IntegralCriticalTotalCompanionBits.valid F (IntegralCriticalFlatEulerBits.next F.toParameters p q) ↔
      IntegralCriticalTotalCompanionBits.valid F q := by
  change (birth F.toParameters (IntegralCriticalFlatEulerBits.next F.toParameters p q) <
    (F.rules (RankedHistoryTask.root (IntegralCriticalFlatEulerBits.next F.toParameters p q))).length) ↔ _
  rw [IntegralCriticalFlatEulerBits.next_birth, IntegralCriticalFlatEulerBits.next_root]
  rfl

theorem companion_next (F : Scripts) (p : Phase) (q : List Bool) :
    IntegralCriticalFlatHeightBits.companionValue F (IntegralCriticalFlatEulerBits.next F.toParameters p q) =
      IntegralCriticalFlatHeightBits.companionValue F q := by
  by_cases hv : IntegralCriticalTotalCompanionBits.valid F q
  · have HN := (valid_next F p q).mpr hv
    unfold IntegralCriticalFlatHeightBits.companionValue
    rw [dite_eq_left HN, dite_eq_left hv,
      IntegralCriticalTotalCompanionBits.creator_invariance F _ q HN hv
        (IntegralCriticalFlatEulerBits.next_root F.toParameters p q)
        (IntegralCriticalFlatEulerBits.next_birth F.toParameters p q),
      IntegralCriticalFlatEulerBits.next_get, IntegralCriticalFlatEulerBits.next_get,
      IntegralCriticalFlatEulerBits.next_modulus]
  · have HN : ¬ IntegralCriticalTotalCompanionBits.valid F (IntegralCriticalFlatEulerBits.next F.toParameters p q) :=
      fun h => hv ((valid_next F p q).mp h)
    unfold IntegralCriticalFlatHeightBits.companionValue
    rw [dite_eq_right HN, dite_eq_right hv]

theorem companion_value (F : Scripts) (q : List Bool) :
    IntegralCriticalActualModelBits.value F (IntegralCriticalFlatEulerBits.next F.toParameters .companion q) =
      IntegralCriticalFlatHeightBits.companionValue F q := by
  by_cases hv : IntegralCriticalTotalCompanionBits.valid F q
  · rw [IntegralCriticalActualModelBits.value_phase F .companion _ ((valid_next F .companion q).mpr hv)
      (IntegralCriticalFlatEulerBits.next_phase F.toParameters .companion q)]
    exact companion_next F .companion q
  · have HN : ¬ IntegralCriticalTotalCompanionBits.valid F (IntegralCriticalFlatEulerBits.next F.toParameters .companion q) :=
      fun h => hv ((valid_next F .companion q).mp h)
    rw [IntegralCriticalActualModelBits.value, ite_eq_right HN]
    unfold IntegralCriticalFlatHeightBits.companionValue
    rw [dite_eq_right hv]

end LeanCanny.Algebra.IntegralCriticalActualEntryBits
