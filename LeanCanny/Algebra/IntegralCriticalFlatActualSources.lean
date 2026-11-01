/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingAccess
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingLeading
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingDenominator
public import LeanCanny.Algebra.IntegralCriticalFlatReductionEntry
public import LeanCanny.Algebra.IntegralCriticalFlatReductionPower
public import LeanCanny.Algebra.IntegralCriticalFlatRelativeFactorLocal
/-! # One total actual source for the flat critical arithmetic stages

All native access records below use the same root script and task fields.
They do not choose a different constant creating query for each valid word.
The missing-birth branch is the total source's fixed integer base algebra.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualSources
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false
abbrev Scripts := IntegralCriticalFlatHeightBits.Scripts

structure Controls (F : Scripts) : Prop where
  task : IntegralCriticalFlatHeightBits.Access F
  metadata : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F)
  objective : BinaryFn (IntegralCriticalTotalCreatingBits.commandObjective F)
  coordinate : BinaryFn (IntegralCriticalTotalCreatingBits.commandCoordinate F)

noncomputable def criticalAccess (F : Scripts) (h : Controls F) : IntegralClearedCriticalBits.Access (IntegralCriticalTotalCreatingBits.source F) :=
  IntegralCriticalTotalCreatingBits.criticalAccess F h.task h.metadata h.objective h.coordinate
noncomputable def eulerAccess (F : Scripts) (h : Controls F) : IntegralEulerBits.Access (IntegralCriticalTotalCreatingBits.euler F) :=
  IntegralCriticalTotalCreatingBits.access F h.task h.metadata h.objective
noncomputable def relative (F : Scripts) : IntegralPurePowerActionBits.Source :=
  IntegralClearedCriticalBits.relativeSource (IntegralCriticalTotalCreatingBits.source F)
noncomputable def relativeAccess (F : Scripts) (h : Controls F) : IntegralPurePowerReductionBits.Access (relative F) :=
  IntegralClearedCriticalBits.relativeAccess (IntegralCriticalTotalCreatingBits.source F) (criticalAccess F h)
noncomputable def reduction (F : Scripts) : IntegralReductionActionBits.Source := IntegralPurePowerActionBits.reductionSource (relative F)
noncomputable def reductionAccess (F : Scripts) (h : Controls F) : IntegralBerkowitzBlockBits.Access (reduction F).toSource :=
  IntegralPurePowerReductionBits.reductionAccess (relative F) (relativeAccess F h)
noncomputable def characteristic (F : Scripts) : IntegralBerkowitzBlockBits.Source := IntegralReductionActionBits.actionSource (reduction F)
noncomputable def characteristicAccess (F : Scripts) (h : Controls F) : IntegralBerkowitzBlockBits.Access (characteristic F) :=
  IntegralReductionActionBits.actionAccess (reduction F) (reductionAccess F h)

theorem reductionControls (F : Scripts) (h : Controls F) : IntegralReductionActionBits.Controls (reduction F) :=
  IntegralPurePowerActionBits.controls (relative F) (relativeAccess F h).layout
    (relativeAccess F h).coordinate (relativeAccess F h).bound

theorem scalar_FP (F : Scripts) (h : Controls F) :
    (fun c => residueBits ((relative F).leading c : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters c))) ∈ FP := by
  have HQ : (eulerAccess F h).denominator ∈ FP :=
    mem_FP_of_eq (IntegralCriticalTotalCreatingBits.denominator_FP F h.task h.metadata)
      (fun c => ((eulerAccess F h).denominator_eq c).symm)
  have HA : (eulerAccess F h).leading ∈ FP :=
    mem_FP_of_eq (IntegralCriticalTotalCreatingBits.leading_FP F h.task h.metadata)
      (fun c => ((eulerAccess F h).leading_eq c).symm)
  exact IntegralCriticalLeadingBits.value_FP _ (eulerAccess F h).toGradient.toFrozen HQ HA

theorem relativeLeading_FP (F : Scripts) (h : Controls F) : (relativeAccess F h).leading ∈ FP :=
  mem_FP_of_eq (scalar_FP F h) (fun c => ((relativeAccess F h).leading_eq c).symm)

theorem action_controls (F : Scripts) (h : Controls F) :
    (IntegralCriticalFlatActionBits.program F.toParameters (reduction F)).Controls :=
  IntegralCriticalFlatActionBits.controls F.toParameters h.task.toAccess (reduction F)
    (reductionAccess F h) (reductionControls F h)

theorem reductionEntry_controls (F : Scripts) (h : Controls F) :
    (IntegralCriticalFlatReductionEntryBits.program F.toParameters (relative F) (relativeAccess F h)).Controls :=
  IntegralCriticalFlatReductionEntryBits.controls F.toParameters h.task.toAccess (relative F)
    (relativeAccess F h) (relativeLeading_FP F h)

theorem relativeFactor_controls (F : Scripts) (h : Controls F) :
    (IntegralCriticalFlatRelativeFactorBits.program F.toParameters (characteristic F)).Controls :=
  IntegralCriticalFlatRelativeFactorBits.controls F.toParameters h.task.toAccess (characteristic F)
    (characteristicAccess F h)

theorem reductionPower_certificates (F : Scripts) (h : Controls F) :
    (IntegralCriticalFlatReductionPowerBits.controller F.toParameters h.task.toAccess (reduction F)
      (reductionAccess F h) (reductionControls F h)).Certificates
        (encQ := Turing.MultiTapeTM.encBits) (encS := Turing.MultiTapeTM.encBits) :=
  IntegralCriticalFlatReductionPowerBits.certificates F.toParameters h.task.toAccess (reduction F)
    (reductionAccess F h) (reductionControls F h)

theorem relative_modulus (F : Scripts) (c : List Bool) :
    (relative F).modulus c = IntegralCriticalHistoryTask.modulus F.toParameters c := rfl

theorem characteristic_modulus (F : Scripts) (c : List Bool) :
    (characteristic F).modulus c = IntegralCriticalHistoryTask.modulus F.toParameters c := rfl

theorem polynomial_value (F : Scripts) :
    IntegralScaledCharacteristicBits.value (characteristic F) (relative F).leading
      (fun c => (relative F).layout.bound c + 1) = (IntegralCriticalTotalCreatingBits.source F).value :=
  IntegralPurePowerActionBits.polynomial_value (relative F)

end LeanCanny.Algebra.IntegralCriticalFlatActualSources
