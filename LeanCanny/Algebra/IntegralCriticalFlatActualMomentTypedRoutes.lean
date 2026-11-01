/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActualMomentRoutes
/-! # The three typed augmented blocks use actual phase-nineteen entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualMomentRoutes
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralBerkowitzBlockBits IntegralCriticalFlatActualMomentBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] characteristic characteristicAccess IntegralCriticalTotalCreatingBits.atFamily

noncomputable abbrev access (F : Scripts) (h : Controls F) :=
  IntegralCriticalFlatMomentBits.access F.toParameters h.task.toAccess (characteristic F) (characteristicAccess F h)

theorem rowTask_value (F : Scripts) (h : Controls F) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c)
    (i : Fin ((moment F).dimension c)) (r t : Fin ((moment F).rank c)) :
    actionValue F (IntegralCriticalFlatMomentTasks.rowTask F.toParameters (characteristic F)
      (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val))) =
      (access F h).row (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val)) := by
  let s := stage (characteristic F) (IntegralCriticalFlatMomentBits.packet F.toParameters c)
  let parent := original (IntegralCriticalFlatMomentBits.packet F.toParameters c)
  have HV : IntegralCriticalTotalCompanionBits.valid F parent := by
    change IntegralCriticalTotalCompanionBits.valid F (original (IntegralCriticalFlatMomentBits.packet F.toParameters c))
    rw [IntegralCriticalFlatMomentBits.packet_parent]
    exact hv
  have HI : i.val < (characteristic F).dimension parent - s - 1 := i.isLt
  let u : Fin ((characteristic F).dimension parent) := ⟨s, by omega⟩
  let v : Fin ((characteristic F).dimension parent) := ⟨s + 1 + i.val, by omega⟩
  change actionValue F (IntegralCriticalFlatBerkowitzQuery.entryWriter F.toParameters (characteristic F)
    (rowQuery (characteristic F) (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet F.toParameters)
      (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val))))) = _
  rw [IntegralBlockMomentBits.requery_context, rowQuery_packet ]
  rw [(access F h).row_eq]
  exact actionChild_value F parent HV u v r t

theorem columnTask_value (F : Scripts) (h : Controls F) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c)
    (i : Fin ((moment F).dimension c)) (r t : Fin ((moment F).rank c)) :
    actionValue F (IntegralCriticalFlatMomentTasks.columnTask F.toParameters (characteristic F)
      (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val))) =
      (access F h).column (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val)) := by
  let s := stage (characteristic F) (IntegralCriticalFlatMomentBits.packet F.toParameters c)
  let parent := original (IntegralCriticalFlatMomentBits.packet F.toParameters c)
  have HV : IntegralCriticalTotalCompanionBits.valid F parent := by
    change IntegralCriticalTotalCompanionBits.valid F (original (IntegralCriticalFlatMomentBits.packet F.toParameters c))
    rw [IntegralCriticalFlatMomentBits.packet_parent]
    exact hv
  have HI : i.val < (characteristic F).dimension parent - s - 1 := i.isLt
  let u : Fin ((characteristic F).dimension parent) := ⟨s, by omega⟩
  let v : Fin ((characteristic F).dimension parent) := ⟨s + 1 + i.val, by omega⟩
  change actionValue F (IntegralCriticalFlatBerkowitzQuery.entryWriter F.toParameters (characteristic F)
    (columnQuery (characteristic F) (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet F.toParameters)
      (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val))))) = _
  rw [IntegralBlockMomentBits.requery_context, columnQuery_packet ]
  rw [(access F h).column_eq]
  exact actionChild_value F parent HV v u r t

theorem matrixTask_value (F : Scripts) (h : Controls F) (c : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F c)
    (i j : Fin ((moment F).dimension c)) (r t : Fin ((moment F).rank c)) :
    actionValue F (IntegralCriticalFlatMomentTasks.matrixTask F.toParameters (characteristic F)
      (pair (IntegralBlockMomentBits.context c r.val t.val)
        (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      (access F h).entry (pair (IntegralBlockMomentBits.context c r.val t.val)
        (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) := by
  let s := stage (characteristic F) (IntegralCriticalFlatMomentBits.packet F.toParameters c)
  let parent := original (IntegralCriticalFlatMomentBits.packet F.toParameters c)
  have HV : IntegralCriticalTotalCompanionBits.valid F parent := by
    change IntegralCriticalTotalCompanionBits.valid F (original (IntegralCriticalFlatMomentBits.packet F.toParameters c))
    rw [IntegralCriticalFlatMomentBits.packet_parent]
    exact hv
  have HI : i.val < (characteristic F).dimension parent - s - 1 := i.isLt
  have HJ : j.val < (characteristic F).dimension parent - s - 1 := j.isLt
  let u : Fin ((characteristic F).dimension parent) := ⟨s + 1 + i.val, by omega⟩
  let v : Fin ((characteristic F).dimension parent) := ⟨s + 1 + j.val, by omega⟩
  change actionValue F (IntegralCriticalFlatBerkowitzQuery.entryWriter F.toParameters (characteristic F)
    (matrixQuery (characteristic F) (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet F.toParameters)
      (pair (IntegralBlockMomentBits.context c r.val t.val)
        (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))))) = _
  rw [IntegralBlockMomentBits.requery_context, matrixQuery_packet ]
  rw [(access F h).entry_eq]
  exact actionChild_value F parent HV u v r t

end LeanCanny.Algebra.IntegralCriticalFlatActualMomentRoutes
