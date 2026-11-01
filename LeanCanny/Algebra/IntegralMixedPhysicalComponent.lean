/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalUpperModel
public import LeanCanny.Algebra.IntegralMixedPhysicalContextLowerReplies
/-! # One canonical component model for actual physical arithmetic -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalComponentBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalUpperBits
set_option backward.isDefEq.respectTransparency false

noncomputable def component (P : Parameters) (F : Family) : Phase → List Bool → List Bool
  | .reductionEntry => IntegralMixedPhysicalMatrixBits.reductionEntry P F
  | .reductionPower => powerValue P F
  | .actionEntry => IntegralMixedPhysicalMatrixBits.actionEntry P F
  | .momentEntry => momentEntry P F
  | .momentPower => momentValue P F
  | .relativeFactor => IntegralMixedPhysicalMatrixBits.relativeFactor P F
  | .relativePower => (characteristic P F).value
  | .criticalCoefficient => (critical P F).value
  | p => IntegralMixedPhysicalContextLowerModelBits.component P F p

theorem component_lower (P : Parameters) (F : Family) (p : Phase) (q : List Bool) (hp : p.code ≤ 16) :
    component P F p q = IntegralMixedPhysicalContextLowerModelBits.component P F p q := by
  cases p <;> simp_all only [Phase.code, component] <;> omega

theorem component_upper (P : Parameters) (F : Family) (p : Phase) (q : List Bool) (hp : 17 ≤ p.code) :
    component P F p q = IntegralMixedPhysicalUpperDispatcherBits.component P F p q := by
  cases p <;> simp_all only [Phase.code, component, IntegralMixedPhysicalUpperDispatcherBits.component,
    IntegralMixedPhysicalContextLowerModelBits.component, IntegralMixedPhysicalContextStageReplyBits.component] <;> omega

abbrev Matches (P : Parameters) (F : Family) (reply : List Bool → List Bool) : Prop :=
  ∀ p q, p.code ≤ 25 → IntegralMixedPhysicalContextBits.selected P p q = true → reply q = component P F p q

theorem lower_matches (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    IntegralMixedPhysicalContextLowerModelBits.Matches P F reply := by
  intro p q hp hq
  exact (hm p q (hp.trans (by decide)) hq).trans (component_lower P F p q hp)

theorem component_canonical (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = component P F p q := by
  cases p
  case reductionEntry => exact IntegralMixedPhysicalUpperCanonicalBits.reductionEntry_canonical P F q
  case reductionPower => exact IntegralMixedPhysicalUpperCanonicalBits.reductionPower_canonical P F q
  case actionEntry => exact IntegralMixedPhysicalUpperCanonicalBits.action_canonical P F q
  case momentEntry => exact IntegralMixedPhysicalUpperCanonicalBits.momentEntry_canonical P F q
  case momentPower => exact IntegralMixedPhysicalUpperCanonicalBits.momentPower_canonical P F q
  case relativeFactor => exact IntegralMixedPhysicalUpperCanonicalBits.relativeFactor_canonical P F q
  case relativePower => exact IntegralMixedPhysicalUpperCanonicalBits.relativePower_canonical P F q
  case criticalCoefficient => exact IntegralMixedPhysicalUpperCanonicalBits.critical_canonical P F q
  all_goals
    simp only [component]
    exact IntegralMixedPhysicalContextLowerModelBits.component_canonical P F _ q
end LeanCanny.Algebra.IntegralMixedPhysicalComponentBits
