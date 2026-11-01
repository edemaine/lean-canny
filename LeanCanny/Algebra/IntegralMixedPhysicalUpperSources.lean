/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalSnapshot
public import LeanCanny.Algebra.IntegralMixedPhysicalCaps
public import LeanCanny.Algebra.IntegralReductionActionFreeze
/-! # Actual upper arithmetic sources over the physical mixed prefix

All metadata access records are derived from the same selected old algebra.
The leading and lower entries remain semantic values, with no evaluator
premise or FP leading shortcut. Constant-query snapshots expose matrix
geometry separately from fresh arithmetic task fields.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev critical (P : Parameters) (F : Family) := IntegralMixedPhysicalTaskBits.source P F
noncomputable def criticalAccess (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) : IntegralClearedCriticalBits.Access (critical P F) :=
  IntegralMixedPhysicalTaskBits.access P a F h

noncomputable def relative (P : Parameters) (F : Family) := IntegralClearedCriticalBits.relativeSource (critical P F)
noncomputable def relativeAccess (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) : IntegralPurePowerReductionBits.Access (relative P F) :=
  IntegralClearedCriticalBits.relativeAccess (critical P F) (criticalAccess P a F h)

noncomputable def reduction (P : Parameters) (F : Family) := IntegralPurePowerActionBits.reductionSource (relative P F)
noncomputable def reductionAccess (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) : IntegralBerkowitzBlockBits.Access (reduction P F).toSource :=
  IntegralPurePowerReductionBits.reductionAccess (relative P F) (relativeAccess P a F h)

noncomputable def characteristic (P : Parameters) (F : Family) := IntegralReductionActionBits.actionSource (reduction P F)
noncomputable def characteristicAccess (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) : IntegralBerkowitzBlockBits.Access (characteristic P F) :=
  IntegralReductionActionBits.actionAccess (reduction P F) (reductionAccess P a F h)

theorem reduction_controls (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedPhysicalQueryBits.InputMetadata F) : IntegralReductionActionBits.Controls (reduction P F) :=
  IntegralPurePowerActionBits.controls (relative P F) (relativeAccess P a F h).layout
    (relativeAccess P a F h).coordinate (relativeAccess P a F h).bound

noncomputable def relativeAt (P : Parameters) (F : Family) (q : List Bool) :=
  IntegralClearedCriticalBits.relativeSource (IntegralMixedPhysicalSnapshotBits.family P F q)
noncomputable def reductionAt (P : Parameters) (F : Family) (q : List Bool) :=
  IntegralPurePowerActionBits.reductionSource (relativeAt P F q)
noncomputable def characteristicAt (P : Parameters) (F : Family) (q : List Bool) :=
  IntegralReductionActionBits.actionSource (reductionAt P F q)

theorem reduction_matrix (P : Parameters) (F : Family) (q : List Bool) :
    (reduction P F).matrix q = (reductionAt P F q).matrix [] := rfl
theorem characteristic_matrix (P : Parameters) (F : Family) (q : List Bool) :
    (characteristic P F).matrix q = (characteristicAt P F q).matrix [] := rfl
theorem characteristic_value (P : Parameters) (F : Family) (q : List Bool) :
    (characteristic P F).value q = (characteristicAt P F q).value [] := rfl
theorem freeze_reduction (P : Parameters) (F : Family) (q : List Bool) :
    IntegralReductionActionFreezeBits.freeze (reduction P F) q = reductionAt P F q := rfl

theorem characteristic_next (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    (characteristic P F).value (IntegralCriticalFlatEulerBits.next P p q) = (characteristic P F).value q := by
  rw [characteristic_value, characteristic_value]
  unfold characteristicAt reductionAt relativeAt
  rw [IntegralMixedPhysicalSnapshotBits.family_next]

end LeanCanny.Algebra.IntegralMixedPhysicalUpperBits
