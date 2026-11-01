/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalCreatingRetarget
/-! # Actual Euler and reduction matrices ignore output query fields -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalQuerySnapshotBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalScriptQueryBits
set_option backward.isDefEq.respectTransparency false

noncomputable def relative (F : Families) (q : Queries F) := IntegralClearedCriticalBits.relativeSource (source F q)
noncomputable def reduction (F : Families) (q : Queries F) := IntegralPurePowerActionBits.reductionSource (relative F q)
noncomputable def action (F : Families) (q : Queries F) := IntegralReductionActionBits.actionSource (reduction F q)
noncomputable def canonicalRelative (F : IntegralHistoryCriticalBits.Family) := IntegralClearedCriticalBits.relativeSource (IntegralHistoryCriticalBits.source F)
noncomputable def canonicalReduction (F : IntegralHistoryCriticalBits.Family) := IntegralPurePowerActionBits.reductionSource (canonicalRelative F)
noncomputable def canonicalAction (F : IntegralHistoryCriticalBits.Family) := IntegralReductionActionBits.actionSource (canonicalReduction F)

theorem lower_snapshot (F : Families) (q : Queries F) (c : List Bool)
    (i : Fin ((IntegralHistoryCriticalBits.source (F c)).free [])) :
    letI := (IntegralHistoryCriticalBits.source (F c)).ring []
    (source F q).toEuler.lowerPolynomial c i = (IntegralHistoryCriticalBits.source (F c)).toEuler.lowerPolynomial [] i := rfl

theorem reduction_matrix_snapshot (F : Families) (q : Queries F) (c : List Bool) :
    (reduction F q).matrix c = (canonicalReduction (F c)).matrix [] := rfl

theorem action_matrix_snapshot (F : Families) (q : Queries F) (c : List Bool) :
    (action F q).matrix c = (canonicalAction (F c)).matrix [] := rfl

theorem reduction_entry_snapshot (F : Families) (q : Queries F) (c : List Bool)
    (i j : Fin ((canonicalReduction (F c)).dimension [])) :
    (reduction F q).toSource.entryMatrix c i j = (canonicalReduction (F c)).toSource.entryMatrix [] i j := rfl

theorem action_entry_snapshot (F : Families) (q : Queries F) (c : List Bool)
    (i j : Fin ((canonicalAction (F c)).dimension [])) :
    (action F q).entryMatrix c i j = (canonicalAction (F c)).entryMatrix [] i j := rfl

theorem action_coefficient_snapshot (F : Families) (q : Queries F) (c : List Bool) (k : ℕ) :
    (action F q).coefficientMatrix c k = (canonicalAction (F c)).coefficientMatrix [] k := rfl
theorem power_matrix_snapshot (F : Families) (q : Queries F) (c : List Bool) :
    (action F q).powerMatrix c = (canonicalAction (F c)).powerMatrix [] := rfl

end LeanCanny.Algebra.IntegralCriticalQuerySnapshotBits
