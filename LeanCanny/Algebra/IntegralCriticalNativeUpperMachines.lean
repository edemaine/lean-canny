/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeUpperData
/-! # Native local machines for phases seventeen through twenty-six -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relative relativeAccess reduction reductionAccess characteristic characteristicAccess
  IntegralCriticalTotalCreatingBits.atFamily

noncomputable def stage17 (F : Scripts) (h : Controls F) : Machine :=
  single F h (IntegralCriticalFlatReductionEntryBits.program F.toParameters (relative F) (relativeAccess F h))
    ((IntegralCriticalFlatReductionEntryBits.program F.toParameters (relative F) (relativeAccess F h)).certificates
      (reductionEntry_controls F h))
    (selectedFinite F .reductionEntry (reductionSize F))
    (selectedFinite_FP F h .reductionEntry _ (reductionSize_binary F h)) (IntegralCriticalFlatActualReductionEntryBits.value F)

noncomputable def stage19 (F : Scripts) (h : Controls F) : Machine :=
  single F h (IntegralCriticalFlatActionBits.program F.toParameters (reduction F))
    ((IntegralCriticalFlatActionBits.program F.toParameters (reduction F)).certificates (action_controls F h))
    (selectedFinite F .actionEntry (reductionSize F))
    (selectedFinite_FP F h .actionEntry _ (reductionSize_binary F h)) (IntegralCriticalFlatActualActionBits.value F)

noncomputable def stage21 (F : Scripts) (h : Controls F) : Machine :=
  single F h (IntegralCriticalFlatMomentEntryBits.program F.toParameters h.task.toAccess (characteristic F) (characteristicAccess F h))
    ((IntegralCriticalFlatMomentEntryBits.program F.toParameters h.task.toAccess (characteristic F) (characteristicAccess F h)).certificates
      (IntegralCriticalFlatMomentEntryBits.controls _ _ _ _))
    (selected F .momentEntry) (selected_FP F h .momentEntry) (IntegralCriticalFlatActualMomentBits.value F)

noncomputable def stage23 (F : Scripts) (h : Controls F) : Machine :=
  single F h (IntegralCriticalFlatRelativeFactorBits.program F.toParameters (characteristic F))
    ((IntegralCriticalFlatRelativeFactorBits.program F.toParameters (characteristic F)).certificates (relativeFactor_controls F h))
    (selectedFinite F .relativeFactor (factorSize F))
    (selectedFinite_FP F h .relativeFactor _ (factorSize_binary F h)) (IntegralCriticalFlatActualRelativeFactorBits.value F)

noncomputable def stage25 (F : Scripts) (h : Controls F) : Machine :=
  single F h (IntegralCriticalFlatActualCoefficientBits.program F)
    ((IntegralCriticalFlatActualCoefficientBits.program F).certificates (IntegralCriticalFlatActualCoefficientBits.controls F h))
    (selected F .criticalCoefficient) (selected_FP F h .criticalCoefficient) (IntegralCriticalTotalCreatingBits.coefficientValue F)

noncomputable def stage26 (F : Scripts) (h : Controls F) : Machine :=
  single F h (IntegralCriticalTotalCompanionBits.program F)
    ((IntegralCriticalTotalCompanionBits.program F).certificates (IntegralCriticalTotalCompanionBits.program_controls F h.task h.metadata))
    (selected F .companion) (selected_FP F h .companion) (IntegralCriticalFlatHeightBits.companionValue F)

noncomputable def stage18 (F : Scripts) (h : Controls F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := encBits
  controller := IntegralCriticalFlatReductionPowerBits.controller F.toParameters h.task.toAccess (reduction F)
    (reductionAccess F h) (reductionControls F h)
  certificates := reductionPower_certificates F h
  selected := selected F .reductionPower
  selected_FP := selected_FP F h .reductionPower
  model := IntegralCriticalTotalActionSnapshotBits.powerValue F
  clock := IntegralCriticalFlatReductionPowerBits.clock F.toParameters (reduction F)
  clock_binary := IntegralCriticalFlatReductionPowerBits.clock_binary F.toParameters h.task.toAccess (reduction F)
    (reductionAccess F h) (reductionControls F h)
  stateBound := IntegralCriticalFlatReductionPowerBits.stateBound F.toParameters (reduction F)
  stateBound_unary := IntegralCriticalFlatReductionPowerBits.stateBound_unary F.toParameters h.task.toAccess (reduction F)
    (reductionAccess F h) (reductionControls F h)

noncomputable def stage22 (F : Scripts) (h : Controls F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := encBits
  controller := IntegralCriticalFlatMomentBits.controller F.toParameters h.task.toAccess (characteristic F) (characteristicAccess F h)
  certificates := IntegralCriticalFlatMomentBits.certificates _ _ _ _
  selected := selected F .momentPower
  selected_FP := selected_FP F h .momentPower
  model := IntegralCriticalTotalMomentValueSnapshotBits.value F
  clock := IntegralCriticalFlatMomentBits.clock F.toParameters (characteristic F)
  clock_binary := IntegralCriticalFlatMomentBits.clock_binary F.toParameters h.task.toAccess (characteristic F) (characteristicAccess F h)
  stateBound := IntegralCriticalFlatMomentBits.stateBound F.toParameters (characteristic F)
  stateBound_unary := IntegralCriticalFlatMomentBits.stateBound_unary F.toParameters h.task.toAccess (characteristic F) (characteristicAccess F h)

noncomputable def stage24 (F : Scripts) (h : Controls F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := encBits
  controller := IntegralCriticalFlatActualRelativeBits.controller F h
  certificates := IntegralCriticalFlatActualRelativeBits.certificates F h
  selected := selected F .relativePower
  selected_FP := selected_FP F h .relativePower
  model := (characteristic F).value
  clock := IntegralCriticalFlatActualRelativeBits.clock F
  clock_binary := IntegralCriticalFlatActualRelativeBits.clock_binary F h
  stateBound := IntegralCriticalFlatActualRelativeBits.stateBound F
  stateBound_unary := IntegralCriticalFlatActualRelativeBits.stateBound_unary F h

end LeanCanny.Algebra.IntegralCriticalNativeUpperBits
