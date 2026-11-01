/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualModel
public import LeanCanny.Algebra.IntegralCriticalNativeLowerModel
public import LeanCanny.Algebra.IntegralCriticalNativeUpperData
/-! # The single actual residue model satisfies both dispatcher interfaces -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeModelBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalActualModelBits
set_option backward.isDefEq.respectTransparency false

private theorem lower_component (F : Scripts) (p : Phase) (q : List Bool) (hp : p.code ≤ 16) :
    component F p q = IntegralCriticalNativeLowerBits.model F p q := by
  cases p <;> norm_num only [Phase.code] at hp <;> rfl

theorem lower_matches (F : Scripts) : IntegralCriticalNativeLowerBits.Matches F (residue F) := by
  intro p q hp hv hphase
  change residueBits (residue F q) = _
  exact ((residue_value F q).trans (value_phase F p q hv hphase)).trans (lower_component F p q hp)

theorem upper_matches (F : Scripts) : IntegralCriticalNativeUpperBits.Matches F (residue F) where
  lower q hv hp := by
    change residueBits (residue F q) = _
    exact (residue_value F q).trans (value_phase F .eulerLower q hv hp)
  reductionEntry q hv hp := by
    change residueBits (residue F q) = _
    exact (residue_value F q).trans (value_phase F .reductionEntry q hv hp)
  reductionPower q hv hp := by
    change residueBits (residue F q) = _
    exact (residue_value F q).trans (value_phase F .reductionPower q hv hp)
  action q hv hp := by
    change residueBits (residue F q) = _
    exact (residue_value F q).trans (value_phase F .actionEntry q hv hp)
  momentEntry q hv hp := by
    change residueBits (residue F q) = _
    exact (residue_value F q).trans (value_phase F .momentEntry q hv hp)
  moment q hv hp := by
    change residueBits (residue F q) = _
    exact (residue_value F q).trans (value_phase F .momentPower q hv hp)
  relativeFactor q hv hp := by
    change residueBits (residue F q) = _
    exact (residue_value F q).trans (value_phase F .relativeFactor q hv hp)
  relativePower q hv hp := by
    change residueBits (residue F q) = _
    exact (residue_value F q).trans (value_phase F .relativePower q hv hp)
  coefficient q hv hp := by
    change residueBits (residue F q) = _
    exact (residue_value F q).trans (value_phase F .criticalCoefficient q hv hp)
  companion q hv hp := by
    change residueBits (residue F q) = _
    exact (residue_value F q).trans (value_phase F .companion q hv hp)

theorem invalid_value (F : Scripts) (q : List Bool) (hv : ¬ IntegralCriticalTotalCompanionBits.valid F q) :
    IntegralCriticalActualModelBits.value F q = [] := by
  rw [IntegralCriticalActualModelBits.value, ite_eq_right hv]

end LeanCanny.Algebra.IntegralCriticalNativeModelBits
