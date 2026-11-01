/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualLowerDispatcher
public import LeanCanny.Algebra.IntegralMixedVirtualLowerModel
/-! # Exact lower phase views of the virtual native dispatcher -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualLowerDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualNativeLowerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedVirtualFoldBits.product
theorem choose_model (M N : Machine) (q : List Bool) :
    (M.choose N).model q = bif M.selected q then M.model q else N.model q := by
  cases hm : M.selected q <;> simp only [Machine.choose, hm] <;> rfl


theorem model_guard (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) (q : List Bool) :
    model P a F h ha q = if active P q = true then (inner P a F h ha).model q else [] := rfl

theorem model_invalid (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) (q : List Bool)
    (hv : ¬IntegralMixedVirtualCaps.valid P q) : model P a F h ha q = [] := by
  apply model_outside
  simp only [active, hv, false_and, decide_false]

theorem stage0_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage0 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .originalCoefficient := rfl

theorem stage0_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage0 P a F h ha).selected = selected P .originalCoefficient := rfl

theorem stage1_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage1 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .derivativeCoefficient := rfl

theorem stage1_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage1 P a F h ha).selected = selectedValid P .derivativeCoefficient := rfl

theorem stage2_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage2 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .clearedHeight := rfl

theorem stage2_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage2 P a F h ha).selected = selectedValid P .clearedHeight := rfl

theorem stage3_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage3 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .monomialFactor := rfl

theorem stage3_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage3 P a F h ha).selected = selectedValid P .monomialFactor := rfl

theorem stage4_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage4 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .factorPower := rfl

theorem stage4_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage4 P a F h ha).selected = selectedValid P .factorPower := rfl

theorem stage5_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage5 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .productEntry := rfl

theorem stage5_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage5 P a F h ha).selected = selectedValid P .productEntry := rfl

theorem stage6_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage6 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .productPower := rfl

theorem stage6_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage6 P a F h ha).selected = selectedValid P .productPower := rfl

theorem stage7_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage7 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .originalGridTerm := rfl

theorem stage7_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage7 P a F h ha).selected = selectedValid P .originalGridTerm := rfl

theorem stage8_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage8 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .clearedGridSum := rfl

theorem stage8_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage8 P a F h ha).selected = selectedValid P .clearedGridSum := rfl

theorem stage9_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage9 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .frozenPowerTerm := rfl

theorem stage9_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage9 P a F h ha).selected = selectedValid P .frozenPowerTerm := rfl

theorem stage10_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage10 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .frozenPowerSum := rfl

theorem stage10_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage10 P a F h ha).selected = selectedValid P .frozenPowerSum := rfl

theorem stage11_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage11 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .frozenConstant := rfl

theorem stage11_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage11 P a F h ha).selected = selectedValid P .frozenConstant := rfl

theorem stage12_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage12 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .frozenLower := rfl

theorem stage12_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage12 P a F h ha).selected = selectedValid P .frozenLower := rfl

theorem stage13_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage13 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .coordinateGradientProduct := rfl

theorem stage13_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage13 P a F h ha).selected = selectedValid P .coordinateGradientProduct := rfl

theorem stage14_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage14 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .eulerSum := rfl

theorem stage14_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage14 P a F h ha).selected = selectedValid P .eulerSum := rfl

theorem stage15_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage15 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .eulerObjective := rfl

theorem stage15_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage15 P a F h ha).selected = selectedValid P .eulerObjective := rfl

theorem stage16_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage16 P a F h ha).model = IntegralMixedVirtualLowerModelBits.component P F .eulerLower := rfl

theorem stage16_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) : (stage16 P a F h ha).selected = selectedValid P .eulerLower := rfl

attribute [local irreducible] stage0 stage1 stage2 stage3 stage4 stage5 stage6 stage7 stage8 stage9 stage10 stage11 stage12 stage13 stage14 stage15 stage16
theorem inner_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F) (q : List Bool) : (inner P a F h ha).model q =
    bif selected P .originalCoefficient q then IntegralMixedVirtualLowerModelBits.component P F .originalCoefficient q else
    bif selectedValid P .derivativeCoefficient q then IntegralMixedVirtualLowerModelBits.component P F .derivativeCoefficient q else
    bif selectedValid P .clearedHeight q then IntegralMixedVirtualLowerModelBits.component P F .clearedHeight q else
    bif selectedValid P .monomialFactor q then IntegralMixedVirtualLowerModelBits.component P F .monomialFactor q else
    bif selectedValid P .factorPower q then IntegralMixedVirtualLowerModelBits.component P F .factorPower q else
    bif selectedValid P .productEntry q then IntegralMixedVirtualLowerModelBits.component P F .productEntry q else
    bif selectedValid P .productPower q then IntegralMixedVirtualLowerModelBits.component P F .productPower q else
    bif selectedValid P .originalGridTerm q then IntegralMixedVirtualLowerModelBits.component P F .originalGridTerm q else
    bif selectedValid P .clearedGridSum q then IntegralMixedVirtualLowerModelBits.component P F .clearedGridSum q else
    bif selectedValid P .frozenPowerTerm q then IntegralMixedVirtualLowerModelBits.component P F .frozenPowerTerm q else
    bif selectedValid P .frozenPowerSum q then IntegralMixedVirtualLowerModelBits.component P F .frozenPowerSum q else
    bif selectedValid P .frozenConstant q then IntegralMixedVirtualLowerModelBits.component P F .frozenConstant q else
    bif selectedValid P .frozenLower q then IntegralMixedVirtualLowerModelBits.component P F .frozenLower q else
    bif selectedValid P .coordinateGradientProduct q then IntegralMixedVirtualLowerModelBits.component P F .coordinateGradientProduct q else
    bif selectedValid P .eulerSum q then IntegralMixedVirtualLowerModelBits.component P F .eulerSum q else
    bif selectedValid P .eulerObjective q then IntegralMixedVirtualLowerModelBits.component P F .eulerObjective q else
    bif selectedValid P .eulerLower q then IntegralMixedVirtualLowerModelBits.component P F .eulerLower q else
    [] := by
  simp only [inner, choose_model, stage0_model, stage0_selected, stage1_model, stage1_selected, stage2_model, stage2_selected, stage3_model, stage3_selected, stage4_model, stage4_selected, stage5_model, stage5_selected, stage6_model, stage6_selected, stage7_model, stage7_selected, stage8_model, stage8_selected, stage9_model, stage9_selected, stage10_model, stage10_selected, stage11_model, stage11_selected, stage12_model, stage12_selected, stage13_model, stage13_selected, stage14_model, stage14_selected, stage15_model, stage15_selected, stage16_model, stage16_selected]
  simp only [zero, ofSingleCall]


theorem model_phase (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : Primitive P F)
    (p : Phase) (q : List Bool) (hp : p.code ≤ 16) (hv : IntegralMixedVirtualCaps.valid P q)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 1) (hq : isPhase p q) :
    model P a F h ha q = IntegralMixedVirtualLowerModelBits.component P F p q := by
  have HA : active P q = true := (active_iff P q).mpr ⟨hv, hr, by change phase q = p.code at hq; omega⟩
  rw [model_guard, ite_eq_left HA, inner_model]
  cases p <;> simp only [Phase.code] at hp
  all_goals try omega
  all_goals simp only [isPhase, Phase.code] at hq
  all_goals simp only [selectedValid, selected, hv, hr, Bool.and_true, Bool.true_and, true_and,
    IntegralMixedRoutineTaskBits.Routine.code, isPhase, hq, Phase.code, Nat.reduceEqDiff, Bool.cond_eq_ite,
    decide_true, decide_false, Bool.false_eq_true, ite_false, ite_true]
end LeanCanny.Algebra.IntegralMixedVirtualLowerDispatcherBits
