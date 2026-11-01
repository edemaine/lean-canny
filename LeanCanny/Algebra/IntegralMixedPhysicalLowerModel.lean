/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalLowerDispatcher
/-! # Exact selected model of the physical lower dispatcher -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalLowerDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits IntegralMixedPhysicalContextBits NativeControllerBranch
open IntegralMixedPhysicalNativeLowerBits (originalScalar)
set_option backward.isDefEq.respectTransparency false

theorem original_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : SpaceFunction (originalScalar P F)) :
    (originalMachine P a F h ha).model = IntegralMixedPhysicalContextLowerModelBits.component P F .originalCoefficient := rfl
theorem original_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (ha : SpaceFunction (originalScalar P F)) :
    (originalMachine P a F h ha).selected = selected P .originalCoefficient := rfl
theorem derivative_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (derivativeMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .derivativeCoefficient := rfl
theorem derivative_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (derivativeMachine P a F h).selected = selected P .derivativeCoefficient := rfl
theorem height_model (P : Parameters) (a : Access P) (F : Family) :
    (heightMachine P a F).model = IntegralMixedPhysicalContextLowerModelBits.component P F .clearedHeight := rfl
theorem height_selected (P : Parameters) (a : Access P) (F : Family) :
    (heightMachine P a F).selected = selected P .clearedHeight := rfl
theorem monomial_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (monomialMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .monomialFactor := rfl
theorem monomial_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (monomialMachine P a F h).selected = selected P .monomialFactor := rfl
theorem factor_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (factorMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .factorPower := rfl
theorem factor_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (factorMachine P a F h).selected = selected P .factorPower := rfl
theorem productEntry_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (productEntryMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .productEntry := rfl
theorem productEntry_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (productEntryMachine P a F h).selected = selected P .productEntry := rfl
theorem product_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (productMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .productPower := rfl
theorem product_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (productMachine P a F h).selected = selected P .productPower := rfl
theorem gridTerm_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (gridTermMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .originalGridTerm := rfl
theorem gridTerm_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (gridTermMachine P a F h).selected = selected P .originalGridTerm := rfl
theorem grid_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (gridMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .clearedGridSum := rfl
theorem grid_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (gridMachine P a F h).selected = selected P .clearedGridSum := rfl
theorem frozenPower_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (frozenPowerMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .frozenPowerTerm := rfl
theorem frozenPower_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (frozenPowerMachine P a F h).selected = selected P .frozenPowerTerm := rfl
theorem frozenSum_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (frozenSumMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .frozenPowerSum := rfl
theorem frozenSum_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (frozenSumMachine P a F h).selected = selected P .frozenPowerSum := rfl
theorem frozenConstant_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (frozenConstantMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .frozenConstant := rfl
theorem frozenConstant_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (frozenConstantMachine P a F h).selected = selected P .frozenConstant := rfl
theorem frozenLower_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (frozenLowerMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .frozenLower := rfl
theorem frozenLower_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (frozenLowerMachine P a F h).selected = selected P .frozenLower := rfl
theorem coordinate_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (coordinateMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .coordinateGradientProduct := by
  simp only [coordinateMachine, IntegralMixedPhysicalContextLowerModelBits.component]
theorem coordinate_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (coordinateMachine P a F h).selected = selected P .coordinateGradientProduct := rfl
theorem sum_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (sumMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .eulerSum := rfl
theorem sum_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (sumMachine P a F h).selected = selected P .eulerSum := rfl
theorem objective_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (objectiveMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .eulerObjective := rfl
theorem objective_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (objectiveMachine P a F h).selected = selected P .eulerObjective := rfl
theorem lower_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (lowerMachine P a F h).model = IntegralMixedPhysicalContextLowerModelBits.component P F .eulerLower := rfl
theorem lower_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (lowerMachine P a F h).selected = selected P .eulerLower := rfl

attribute [local irreducible] originalMachine derivativeMachine heightMachine monomialMachine factorMachine productEntryMachine productMachine gridTermMachine gridMachine frozenPowerMachine frozenSumMachine frozenConstantMachine frozenLowerMachine coordinateMachine sumMachine objectiveMachine lowerMachine

theorem model_phase (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (p : Phase) (q : List Bool) (hp : p.code ≤ 16)
    (hq : selected P p q = true) :
    (machine P a F h ha).model q = IntegralMixedPhysicalContextLowerModelBits.component P F p q := by
  cases p <;> simp only [Phase.code] at hp
  case originalCoefficient =>
    rw [← original_model P a F h ha]
    rw [← original_selected P a F h ha] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .originalCoefficient (originalMachine P a F h ha) (original_selected P a F h ha)) (codes_nodup P a F h ha)
      List.mem_cons_self hq
  case derivativeCoefficient =>
    rw [← derivative_model P a F h]
    rw [← derivative_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .derivativeCoefficient (derivativeMachine P a F h) (derivative_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ List.mem_cons_self) hq
  case clearedHeight =>
    rw [← height_model P a F]
    rw [← height_selected P a F] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .clearedHeight (heightMachine P a F) (height_selected P a F)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) hq
  case monomialFactor =>
    rw [← monomial_model P a F h]
    rw [← monomial_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .monomialFactor (monomialMachine P a F h) (monomial_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) hq
  case factorPower =>
    rw [← factor_model P a F h]
    rw [← factor_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .factorPower (factorMachine P a F h) (factor_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) hq
  case productEntry =>
    rw [← productEntry_model P a F h]
    rw [← productEntry_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .productEntry (productEntryMachine P a F h) (productEntry_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))) hq
  case productPower =>
    rw [← product_model P a F h]
    rw [← product_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .productPower (productMachine P a F h) (product_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))) hq
  case originalGridTerm =>
    rw [← gridTerm_model P a F h]
    rw [← gridTerm_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .originalGridTerm (gridTermMachine P a F h) (gridTerm_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))) hq
  case clearedGridSum =>
    rw [← grid_model P a F h]
    rw [← grid_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .clearedGridSum (gridMachine P a F h) (grid_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))) hq
  case frozenPowerTerm =>
    rw [← frozenPower_model P a F h]
    rw [← frozenPower_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .frozenPowerTerm (frozenPowerMachine P a F h) (frozenPower_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))) hq
  case frozenPowerSum =>
    rw [← frozenSum_model P a F h]
    rw [← frozenSum_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .frozenPowerSum (frozenSumMachine P a F h) (frozenSum_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))))) hq
  case frozenConstant =>
    rw [← frozenConstant_model P a F h]
    rw [← frozenConstant_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .frozenConstant (frozenConstantMachine P a F h) (frozenConstant_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))))) hq
  case frozenLower =>
    rw [← frozenLower_model P a F h]
    rw [← frozenLower_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .frozenLower (frozenLowerMachine P a F h) (frozenLower_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))))))) hq
  case coordinateGradientProduct =>
    rw [← coordinate_model P a F h]
    rw [← coordinate_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .coordinateGradientProduct (coordinateMachine P a F h) (coordinate_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))))))) hq
  case eulerSum =>
    rw [← sum_model P a F h]
    rw [← sum_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .eulerSum (sumMachine P a F h) (sum_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))))))))) hq
  case eulerObjective =>
    rw [← objective_model P a F h]
    rw [← objective_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .eulerObjective (objectiveMachine P a F h) (objective_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))))))))))) hq
  case eulerLower =>
    rw [← lower_model P a F h]
    rw [← lower_selected P a F h] at hq
    exact phaseDispatch_model_selected (nodes P a F h ha) zero q
      (node P .eulerLower (lowerMachine P a F h) (lower_selected P a F h)) (codes_nodup P a F h ha)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))))))))))))) hq
  all_goals omega

theorem model_invalid (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (q : List Bool) (hv : ¬ IntegralMixedVirtualCaps.valid P q) :
    (machine P a F h ha).model q = [] := by
  apply phaseDispatch_model_none
  intro b hb
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (originalMachine P a F h ha).selected q = false
    rw [original_selected P a F h ha]
    simp only [selected, hv, false_and, decide_false]
  · change (derivativeMachine P a F h).selected q = false
    rw [derivative_selected P a F h]
    simp only [selected, hv, false_and, decide_false]
  · change (heightMachine P a F).selected q = false
    rw [height_selected P a F]
    simp only [selected, hv, false_and, decide_false]
  · change (monomialMachine P a F h).selected q = false
    rw [monomial_selected P a F h]
    simp only [selected, hv, false_and, decide_false]
  · change (factorMachine P a F h).selected q = false
    rw [factor_selected P a F h]
    simp only [selected, hv, false_and, decide_false]
  · change (productEntryMachine P a F h).selected q = false
    rw [productEntry_selected P a F h]
    simp only [selected, hv, false_and, decide_false]
  · change (productMachine P a F h).selected q = false
    rw [product_selected P a F h]
    simp only [selected, hv, false_and, decide_false]
  · change (gridTermMachine P a F h).selected q = false
    rw [gridTerm_selected P a F h]
    simp only [selected, hv, false_and, decide_false]
  · change (gridMachine P a F h).selected q = false
    rw [grid_selected P a F h]
    simp only [selected, hv, false_and, decide_false]
  · change (frozenPowerMachine P a F h).selected q = false
    rw [frozenPower_selected P a F h]
    simp only [selected, hv, false_and, decide_false]
  · change (frozenSumMachine P a F h).selected q = false
    rw [frozenSum_selected P a F h]
    simp only [selected, hv, false_and, decide_false]
  · change (frozenConstantMachine P a F h).selected q = false
    rw [frozenConstant_selected P a F h]
    simp only [selected, hv, false_and, decide_false]
  · change (frozenLowerMachine P a F h).selected q = false
    rw [frozenLower_selected P a F h]
    simp only [selected, hv, false_and, decide_false]
  · change (coordinateMachine P a F h).selected q = false
    rw [coordinate_selected P a F h]
    simp only [selected, hv, false_and, decide_false]
  · change (sumMachine P a F h).selected q = false
    rw [sum_selected P a F h]
    simp only [selected, hv, false_and, decide_false]
  · change (objectiveMachine P a F h).selected q = false
    rw [objective_selected P a F h]
    simp only [selected, hv, false_and, decide_false]
  · change (lowerMachine P a F h).selected q = false
    rw [lower_selected P a F h]
    simp only [selected, hv, false_and, decide_false]

theorem model_other_context (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (q : List Bool) (hx : get P .slot15 q ≠ 1) :
    (machine P a F h ha).model q = [] := by
  apply phaseDispatch_model_none
  intro b hb
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (originalMachine P a F h ha).selected q = false
    rw [original_selected P a F h ha]
    simp only [selected, hx, and_false, decide_false]
  · change (derivativeMachine P a F h).selected q = false
    rw [derivative_selected P a F h]
    simp only [selected, hx, and_false, decide_false]
  · change (heightMachine P a F).selected q = false
    rw [height_selected P a F]
    simp only [selected, hx, and_false, decide_false]
  · change (monomialMachine P a F h).selected q = false
    rw [monomial_selected P a F h]
    simp only [selected, hx, and_false, decide_false]
  · change (factorMachine P a F h).selected q = false
    rw [factor_selected P a F h]
    simp only [selected, hx, and_false, decide_false]
  · change (productEntryMachine P a F h).selected q = false
    rw [productEntry_selected P a F h]
    simp only [selected, hx, and_false, decide_false]
  · change (productMachine P a F h).selected q = false
    rw [product_selected P a F h]
    simp only [selected, hx, and_false, decide_false]
  · change (gridTermMachine P a F h).selected q = false
    rw [gridTerm_selected P a F h]
    simp only [selected, hx, and_false, decide_false]
  · change (gridMachine P a F h).selected q = false
    rw [grid_selected P a F h]
    simp only [selected, hx, and_false, decide_false]
  · change (frozenPowerMachine P a F h).selected q = false
    rw [frozenPower_selected P a F h]
    simp only [selected, hx, and_false, decide_false]
  · change (frozenSumMachine P a F h).selected q = false
    rw [frozenSum_selected P a F h]
    simp only [selected, hx, and_false, decide_false]
  · change (frozenConstantMachine P a F h).selected q = false
    rw [frozenConstant_selected P a F h]
    simp only [selected, hx, and_false, decide_false]
  · change (frozenLowerMachine P a F h).selected q = false
    rw [frozenLower_selected P a F h]
    simp only [selected, hx, and_false, decide_false]
  · change (coordinateMachine P a F h).selected q = false
    rw [coordinate_selected P a F h]
    simp only [selected, hx, and_false, decide_false]
  · change (sumMachine P a F h).selected q = false
    rw [sum_selected P a F h]
    simp only [selected, hx, and_false, decide_false]
  · change (objectiveMachine P a F h).selected q = false
    rw [objective_selected P a F h]
    simp only [selected, hx, and_false, decide_false]
  · change (lowerMachine P a F h).selected q = false
    rw [lower_selected P a F h]
    simp only [selected, hx, and_false, decide_false]

end LeanCanny.Algebra.IntegralMixedPhysicalLowerDispatcherBits
