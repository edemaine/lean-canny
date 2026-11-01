/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextUpperModel
public import LeanCanny.Algebra.IntegralMixedVirtualContextLowerReplies
/-! # One canonical component model for actual virtual arithmetic -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextComponentBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualContextUpperBits
set_option backward.isDefEq.respectTransparency false

noncomputable def component (P : Parameters) (F : Family) : Phase → List Bool → List Bool
  | .reductionEntry => IntegralMixedVirtualMatrixBits.reductionEntry P F
  | .reductionPower => powerValue P F
  | .actionEntry => IntegralMixedVirtualMatrixBits.actionEntry P F
  | .momentEntry => IntegralMixedVirtualUpperBits.momentEntry P F
  | .momentPower => IntegralMixedVirtualUpperBits.momentValue P F
  | .relativeFactor => IntegralMixedVirtualMatrixBits.relativeFactor P F
  | .relativePower => (IntegralMixedVirtualUpperBits.characteristic P F).value
  | .criticalCoefficient => (IntegralMixedVirtualUpperBits.critical P F).value
  | p => IntegralMixedVirtualContextLowerModelBits.component P F p

theorem component_lower (P : Parameters) (F : Family) (p : Phase) (q : List Bool) (hp : p.code ≤ 16) :
    component P F p q = IntegralMixedVirtualContextLowerModelBits.component P F p q := by
  cases p <;> simp_all only [Phase.code, component] <;> omega

theorem component_upper (P : Parameters) (F : Family) (p : Phase) (q : List Bool) (hp : 17 ≤ p.code) :
    component P F p q = IntegralMixedVirtualContextUpperDispatcherBits.component P F p q := by
  cases p <;> simp_all only [Phase.code, component, IntegralMixedVirtualContextUpperDispatcherBits.component,
    IntegralMixedVirtualContextLowerModelBits.component, IntegralMixedVirtualLowerModelBits.component] <;> omega

abbrev Matches (P : Parameters) (F : Family) (reply : List Bool → List Bool) : Prop :=
  ∀ p q, p.code ≤ 25 → IntegralMixedVirtualContextBits.selected P p q = true → reply q = component P F p q

theorem lower_matches (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    IntegralMixedVirtualContextLowerModelBits.Matches P F reply := by
  intro p q hp hq
  exact (hm p q (hp.trans (by decide)) hq).trans (component_lower P F p q hp)

theorem component_canonical (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = component P F p q := by
  cases p
  case reductionEntry => exact IntegralMixedVirtualCanonicalBits.reductionEntry_canonical P F q
  case reductionPower => exact IntegralMixedVirtualCanonicalBits.reductionPower_canonical P F q
  case actionEntry => exact IntegralMixedVirtualCanonicalBits.action_canonical P F q
  case momentEntry => exact IntegralMixedVirtualCanonicalBits.momentEntry_canonical P F q
  case momentPower => exact IntegralMixedVirtualCanonicalBits.momentPower_canonical P F q
  case relativeFactor => exact IntegralMixedVirtualCanonicalBits.relativeFactor_canonical P F q
  case relativePower => exact IntegralMixedVirtualCanonicalBits.relativePower_canonical P F q
  case criticalCoefficient => exact IntegralMixedVirtualCanonicalBits.critical_canonical P F q
  all_goals
    simp only [component]
    exact IntegralMixedVirtualContextLowerModelBits.component_canonical P F _ q
end LeanCanny.Algebra.IntegralMixedVirtualContextComponentBits
