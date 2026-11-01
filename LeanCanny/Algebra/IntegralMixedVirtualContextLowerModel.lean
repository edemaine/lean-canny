/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextStageReplies
public import LeanCanny.Algebra.IntegralMixedVirtualContextObjective
public import LeanCanny.Algebra.IntegralMixedVirtualContextFrozenConstant
public import LeanCanny.Algebra.IntegralMixedVirtualContextFrozenLower
public import LeanCanny.Algebra.IntegralMixedVirtualContextEulerLower
public import LeanCanny.Algebra.IntegralMixedVirtualContextFolds
public import LeanCanny.Algebra.IntegralMixedVirtualContextCoordinateProduct
public import LeanCanny.Algebra.IntegralMixedVirtualContextFrozenPower
/-! # Actual virtual lower components restricted to producer contexts two through four -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextLowerModelBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false
noncomputable abbrev component := IntegralMixedVirtualLowerModelBits.component
abbrev Matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ p q, p.code ≤ 16 → IntegralMixedVirtualContextBits.selected P p q = true → answer q = component P F p q

theorem component_low (P : Parameters) (F : Family) (p : Phase) (q : List Bool) (hp : p.code ≤ 8) :
    component P F p q = IntegralMixedVirtualContextStageReplyBits.component P F p q := by
  cases p <;> simp_all only [Phase.code, IntegralMixedVirtualLowerModelBits.component,
    IntegralMixedVirtualContextStageReplyBits.component] <;> omega

theorem low_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) (hm : Matches P F answer) :
    IntegralMixedVirtualContextStageReplyBits.Matches P F answer := by
  intro p q hp hq
  exact (hm p q (hp.trans (by decide)) hq).trans (component_low P F p q hp)

theorem component_canonical (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = component P F p q :=
  IntegralMixedVirtualLowerModelBits.component_canonical P F p q
end LeanCanny.Algebra.IntegralMixedVirtualContextLowerModelBits
