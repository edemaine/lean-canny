/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeLowerDispatcher
public import LeanCanny.Algebra.IntegralCriticalActualModel
/-! # Canonical actual component view of the lower native dispatcher -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeLowerDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalActualProductModel.product

theorem choose_model (M N : Machine) (q : List Bool) :
    (M.choose N).model q = bif M.selected q then M.model q else N.model q := by
  cases hm : M.selected q <;> simp only [Machine.choose, hm] <;> rfl

theorem model_guard (F : Scripts) (h : Controls F) (a : Primitive F) (q : List Bool) :
    model F h a q = if IntegralCriticalTotalCompanionBits.valid F q then (inner F h a).model q else [] := by
  change (if decide (IntegralCriticalTotalCompanionBits.valid F q) = true then (inner F h a).model q else []) = _
  simp only [decide_eq_true_eq]

theorem model_invalid (F : Scripts) (h : Controls F) (a : Primitive F) (q : List Bool)
    (hv : ¬ IntegralCriticalTotalCompanionBits.valid F q) : model F h a q = [] := by
  rw [model_guard, ite_eq_right hv]

theorem stage0_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage0 F h a).model = IntegralCriticalNativeLowerBits.model F .originalCoefficient := rfl

theorem stage0_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage0 F h a).selected = selected F .originalCoefficient := rfl

theorem stage1_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage1 F h a).model = IntegralCriticalNativeLowerBits.model F .derivativeCoefficient := rfl

theorem stage1_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage1 F h a).selected = selected F .derivativeCoefficient := rfl

theorem stage2_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage2 F h a).model = IntegralCriticalNativeLowerBits.model F .clearedHeight := rfl

theorem stage2_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage2 F h a).selected = selected F .clearedHeight := rfl

theorem stage3_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage3 F h a).model = IntegralCriticalNativeLowerBits.model F .monomialFactor := rfl

theorem stage3_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage3 F h a).selected = selected F .monomialFactor := rfl

theorem stage4_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage4 F h a).model = IntegralCriticalNativeLowerBits.model F .factorPower := rfl

theorem stage4_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage4 F h a).selected = selected F .factorPower := rfl

theorem stage5_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage5 F h a).model = IntegralCriticalNativeLowerBits.model F .productEntry := rfl

theorem stage5_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage5 F h a).selected = selected F .productEntry := rfl

theorem stage6_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage6 F h a).model = IntegralCriticalNativeLowerBits.model F .productPower := rfl

theorem stage6_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage6 F h a).selected = selected F .productPower := rfl

theorem stage7_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage7 F h a).model = IntegralCriticalNativeLowerBits.model F .originalGridTerm := rfl

theorem stage7_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage7 F h a).selected = selected F .originalGridTerm := rfl

theorem stage8_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage8 F h a).model = IntegralCriticalNativeLowerBits.model F .clearedGridSum := rfl

theorem stage8_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage8 F h a).selected = selected F .clearedGridSum := rfl

theorem stage9_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage9 F h a).model = IntegralCriticalNativeLowerBits.model F .frozenPowerTerm := rfl

theorem stage9_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage9 F h a).selected = selected F .frozenPowerTerm := rfl

theorem stage10_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage10 F h a).model = IntegralCriticalNativeLowerBits.model F .frozenPowerSum := rfl

theorem stage10_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage10 F h a).selected = selected F .frozenPowerSum := rfl

theorem stage11_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage11 F h a).model = IntegralCriticalNativeLowerBits.model F .frozenConstant := rfl

theorem stage11_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage11 F h a).selected = selected F .frozenConstant := rfl

theorem stage12_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage12 F h a).model = IntegralCriticalNativeLowerBits.model F .frozenLower := rfl

theorem stage12_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage12 F h a).selected = selected F .frozenLower := rfl

theorem stage13_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage13 F h a).model = IntegralCriticalNativeLowerBits.model F .coordinateGradientProduct := rfl

theorem stage13_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage13 F h a).selected = selected F .coordinateGradientProduct := rfl

theorem stage14_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage14 F h a).model = IntegralCriticalNativeLowerBits.model F .eulerSum := rfl

theorem stage14_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage14 F h a).selected = selected F .eulerSum := rfl

theorem stage15_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage15 F h a).model = IntegralCriticalNativeLowerBits.model F .eulerObjective := rfl

theorem stage15_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage15 F h a).selected = selected F .eulerObjective := rfl

theorem stage16_model (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage16 F h a).model = IntegralCriticalNativeLowerBits.model F .eulerLower := rfl

theorem stage16_selected (F : Scripts) (h : Controls F) (a : Primitive F) :
    (stage16 F h a).selected = selected F .eulerLower := rfl

attribute [local irreducible] stage0 stage1 stage2 stage3 stage4 stage5 stage6 stage7 stage8 stage9 stage10 stage11 stage12 stage13 stage14 stage15 stage16

theorem inner_model (F : Scripts) (h : Controls F) (a : Primitive F) (q : List Bool) : (inner F h a).model q =
    bif selected F .originalCoefficient q then IntegralCriticalNativeLowerBits.model F .originalCoefficient q else
    bif selected F .derivativeCoefficient q then IntegralCriticalNativeLowerBits.model F .derivativeCoefficient q else
    bif selected F .clearedHeight q then IntegralCriticalNativeLowerBits.model F .clearedHeight q else
    bif selected F .monomialFactor q then IntegralCriticalNativeLowerBits.model F .monomialFactor q else
    bif selected F .factorPower q then IntegralCriticalNativeLowerBits.model F .factorPower q else
    bif selected F .productEntry q then IntegralCriticalNativeLowerBits.model F .productEntry q else
    bif selected F .productPower q then IntegralCriticalNativeLowerBits.model F .productPower q else
    bif selected F .originalGridTerm q then IntegralCriticalNativeLowerBits.model F .originalGridTerm q else
    bif selected F .clearedGridSum q then IntegralCriticalNativeLowerBits.model F .clearedGridSum q else
    bif selected F .frozenPowerTerm q then IntegralCriticalNativeLowerBits.model F .frozenPowerTerm q else
    bif selected F .frozenPowerSum q then IntegralCriticalNativeLowerBits.model F .frozenPowerSum q else
    bif selected F .frozenConstant q then IntegralCriticalNativeLowerBits.model F .frozenConstant q else
    bif selected F .frozenLower q then IntegralCriticalNativeLowerBits.model F .frozenLower q else
    bif selected F .coordinateGradientProduct q then IntegralCriticalNativeLowerBits.model F .coordinateGradientProduct q else
    bif selected F .eulerSum q then IntegralCriticalNativeLowerBits.model F .eulerSum q else
    bif selected F .eulerObjective q then IntegralCriticalNativeLowerBits.model F .eulerObjective q else
    bif selected F .eulerLower q then IntegralCriticalNativeLowerBits.model F .eulerLower q else
    [] := by
  simp only [inner, choose_model, stage0_model, stage0_selected, stage1_model, stage1_selected, stage2_model, stage2_selected, stage3_model, stage3_selected, stage4_model, stage4_selected, stage5_model, stage5_selected, stage6_model, stage6_selected, stage7_model, stage7_selected, stage8_model, stage8_selected, stage9_model, stage9_selected, stage10_model, stage10_selected, stage11_model, stage11_selected, stage12_model, stage12_selected, stage13_model, stage13_selected, stage14_model, stage14_selected, stage15_model, stage15_selected, stage16_model, stage16_selected]
  simp only [zero, ofSingleCall]

theorem model_phase (F : Scripts) (h : Controls F) (a : Primitive F) (p : Phase) (q : List Bool)
    (hp : p.code ≤ 16) (hv : IntegralCriticalTotalCompanionBits.valid F q) (hq : isPhase p q) :
    model F h a q = IntegralCriticalActualModelBits.component F p q := by
  rw [model_guard, ite_eq_left hv, inner_model]
  cases p <;> simp only [Phase.code] at hp
  all_goals try omega
  all_goals simp only [isPhase, Phase.code] at hq
  all_goals simp only [selected, hv, true_and, isPhase, hq, Phase.code, Nat.reduceEqDiff, Bool.cond_eq_ite,
    decide_true, decide_false, Bool.false_eq_true, ite_false, ite_true,
    IntegralCriticalNativeLowerBits.model, IntegralCriticalActualModelBits.component]

end LeanCanny.Algebra.IntegralCriticalNativeLowerDispatcherBits
