/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeFrozenPower
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeCoordinateProduct
public import LeanCanny.Algebra.IntegralMixedPhysicalContextStageReplies
/-! # Exact physical lower component models at all flat query words -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalContextLowerModelBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits
set_option backward.isDefEq.respectTransparency false
noncomputable def component (P : Parameters) (F : Family) : Phase → List Bool → List Bool
  | .frozenPowerTerm => IntegralMixedPhysicalSnapshotBits.frozenTerm P F
  | .frozenPowerSum => IntegralMixedPhysicalSnapshotBits.frozenSum P F
  | .frozenConstant => IntegralMixedPhysicalSnapshotBits.frozenConstant P F
  | .frozenLower => IntegralMixedPhysicalSnapshotBits.frozenLower P F
  | .coordinateGradientProduct => IntegralMixedPhysicalFoldBits.product P F
  | .eulerSum => IntegralMixedPhysicalSnapshotBits.sum P F
  | .eulerObjective => IntegralMixedPhysicalSnapshotBits.objective P F
  | .eulerLower => IntegralMixedPhysicalSnapshotBits.lower P F
  | p => IntegralMixedPhysicalContextStageReplyBits.component P F p

theorem component_low (P : Parameters) (F : Family) (p : Phase) (q : List Bool) (hp : p.code ≤ 8) :
    component P F p q = IntegralMixedPhysicalContextStageReplyBits.component P F p q := by
  cases p <;> simp_all only [Phase.code, component] <;> omega

abbrev Matches (P : Parameters) (F : Family) (reply : List Bool → List Bool) : Prop :=
  ∀ p q, p.code ≤ 16 → IntegralMixedPhysicalContextBits.selected P p q = true → reply q = component P F p q

theorem low_matches (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    IntegralMixedPhysicalContextStageReplyBits.Matches P F reply := by
  intro p q hp hq
  exact (hm p q (hp.trans (by decide)) hq).trans (component_low P F p q hp)

theorem frozenTerm_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalSnapshotBits.frozenTerm P F q := by
  unfold IntegralMixedPhysicalSnapshotBits.frozenTerm
  rw [IntegralFrozenPowerBits.term_packet]
  exact ⟨_, rfl⟩
theorem frozenSum_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalSnapshotBits.frozenSum P F q := by
  rw [IntegralMixedPhysicalSnapshotBits.frozenSum_eq]
  unfold IntegralFrozenPowerBits.Source.sumValue
  exact ⟨_, rfl⟩
theorem frozenConstant_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalSnapshotBits.frozenConstant P F q := by
  rw [IntegralMixedPhysicalSnapshotBits.frozenConstant_eq]
  unfold IntegralFrozenPowerBits.Source.constantValue
  exact ⟨_, rfl⟩
theorem frozenLower_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalSnapshotBits.frozenLower P F q := by
  rw [IntegralMixedPhysicalSnapshotBits.frozenLower_eq]
  unfold IntegralFrozenPowerBits.Source.lowerValue
  exact ⟨_, rfl⟩
theorem coordinateProduct_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalFoldBits.product P F q := by
  rw [IntegralMixedPhysicalFoldBits.product_eq_term, IntegralEulerBits.term_packet]
  exact ⟨_, rfl⟩
theorem sum_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalSnapshotBits.sum P F q := by
  rw [IntegralMixedPhysicalSnapshotBits.sum_eq]
  unfold IntegralEulerBits.Source.sumValue
  exact ⟨_, rfl⟩
theorem objective_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalSnapshotBits.objective P F q := by
  rw [IntegralMixedPhysicalSnapshotBits.objective_eq]
  unfold IntegralEulerBits.Source.objectiveValue
  exact ⟨_, rfl⟩
theorem lower_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = IntegralMixedPhysicalSnapshotBits.lower P F q := by
  rw [IntegralMixedPhysicalSnapshotBits.lower_eq]
  unfold IntegralEulerBits.Source.lowerValue
  exact ⟨_, rfl⟩

theorem component_canonical (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = component P F p q := by
  cases p
  case frozenPowerTerm => exact frozenTerm_canonical P F q
  case frozenPowerSum => exact frozenSum_canonical P F q
  case frozenConstant => exact frozenConstant_canonical P F q
  case frozenLower => exact frozenLower_canonical P F q
  case coordinateGradientProduct => exact coordinateProduct_canonical P F q
  case eulerSum => exact sum_canonical P F q
  case eulerObjective => exact objective_canonical P F q
  case eulerLower => exact lower_canonical P F q
  all_goals
    simp only [component]
    exact IntegralMixedPhysicalContextStageReplyBits.component_canonical P F _ q
end LeanCanny.Algebra.IntegralMixedPhysicalContextLowerModelBits
