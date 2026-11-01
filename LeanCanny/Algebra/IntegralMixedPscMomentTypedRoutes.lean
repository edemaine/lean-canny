/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscMomentRoutes
/-! # The three typed augmented blocks use actual phase-zero entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
attribute [local irreducible] characteristic characteristicAccess

noncomputable abbrev momentAccess (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F) :=
  IntegralCriticalFlatMomentBits.access P a (characteristic P F) (characteristicAccess P a F h)

theorem rowTask_value (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (c : List Bool) (hv : IntegralMixedVirtualCaps.valid P c)
    (i : Fin ((moment P F).dimension c)) (r t : Fin ((moment P F).rank c)) :
    IntegralMixedPscMatrixModel.actionValue P F (IntegralMixedPscMomentTasks.rowTask P (characteristic P F)
      (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val))) =
      (momentAccess P a F h).row (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val)) := by
  let s := stage (characteristic P F) (IntegralCriticalFlatMomentBits.packet P c)
  let parent := original (IntegralCriticalFlatMomentBits.packet P c)
  have HV : IntegralMixedVirtualCaps.valid P parent := by
    change IntegralMixedVirtualCaps.valid P (original (IntegralCriticalFlatMomentBits.packet P c))
    rw [IntegralCriticalFlatMomentBits.packet_parent]
    exact hv
  have HI : i.val < (characteristic P F).dimension parent - s - 1 := i.isLt
  let u : Fin ((characteristic P F).dimension parent) := ⟨s, by omega⟩
  let v : Fin ((characteristic P F).dimension parent) := ⟨s + 1 + i.val, by omega⟩
  change IntegralMixedPscMatrixModel.actionValue P F (IntegralMixedPscMomentTasks.entryWriter P (characteristic P F)
    (rowQuery (characteristic P F) (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P)
      (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val))))) = _
  rw [IntegralBlockMomentBits.requery_context, rowQuery_packet ]
  rw [(momentAccess P a F h).row_eq]
  exact actionChild_value P F g parent HV u v r t

theorem columnTask_value (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (c : List Bool) (hv : IntegralMixedVirtualCaps.valid P c)
    (i : Fin ((moment P F).dimension c)) (r t : Fin ((moment P F).rank c)) :
    IntegralMixedPscMatrixModel.actionValue P F (IntegralMixedPscMomentTasks.columnTask P (characteristic P F)
      (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val))) =
      (momentAccess P a F h).column (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val)) := by
  let s := stage (characteristic P F) (IntegralCriticalFlatMomentBits.packet P c)
  let parent := original (IntegralCriticalFlatMomentBits.packet P c)
  have HV : IntegralMixedVirtualCaps.valid P parent := by
    change IntegralMixedVirtualCaps.valid P (original (IntegralCriticalFlatMomentBits.packet P c))
    rw [IntegralCriticalFlatMomentBits.packet_parent]
    exact hv
  have HI : i.val < (characteristic P F).dimension parent - s - 1 := i.isLt
  let u : Fin ((characteristic P F).dimension parent) := ⟨s, by omega⟩
  let v : Fin ((characteristic P F).dimension parent) := ⟨s + 1 + i.val, by omega⟩
  change IntegralMixedPscMatrixModel.actionValue P F (IntegralMixedPscMomentTasks.entryWriter P (characteristic P F)
    (columnQuery (characteristic P F) (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P)
      (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val))))) = _
  rw [IntegralBlockMomentBits.requery_context, columnQuery_packet ]
  rw [(momentAccess P a F h).column_eq]
  exact actionChild_value P F g parent HV v u r t

theorem matrixTask_value (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (c : List Bool) (hv : IntegralMixedVirtualCaps.valid P c)
    (i j : Fin ((moment P F).dimension c)) (r t : Fin ((moment P F).rank c)) :
    IntegralMixedPscMatrixModel.actionValue P F (IntegralMixedPscMomentTasks.matrixTask P (characteristic P F)
      (pair (IntegralBlockMomentBits.context c r.val t.val)
        (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      (momentAccess P a F h).entry (pair (IntegralBlockMomentBits.context c r.val t.val)
        (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) := by
  let s := stage (characteristic P F) (IntegralCriticalFlatMomentBits.packet P c)
  let parent := original (IntegralCriticalFlatMomentBits.packet P c)
  have HV : IntegralMixedVirtualCaps.valid P parent := by
    change IntegralMixedVirtualCaps.valid P (original (IntegralCriticalFlatMomentBits.packet P c))
    rw [IntegralCriticalFlatMomentBits.packet_parent]
    exact hv
  have HI : i.val < (characteristic P F).dimension parent - s - 1 := i.isLt
  have HJ : j.val < (characteristic P F).dimension parent - s - 1 := j.isLt
  let u : Fin ((characteristic P F).dimension parent) := ⟨s + 1 + i.val, by omega⟩
  let v : Fin ((characteristic P F).dimension parent) := ⟨s + 1 + j.val, by omega⟩
  change IntegralMixedPscMatrixModel.actionValue P F (IntegralMixedPscMomentTasks.entryWriter P (characteristic P F)
    (matrixQuery (characteristic P F) (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P)
      (pair (IntegralBlockMomentBits.context c r.val t.val)
        (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))))) = _
  rw [IntegralBlockMomentBits.requery_context, matrixQuery_packet ]
  rw [(momentAccess P a F h).entry_eq]
  exact actionChild_value P F g parent HV u v r t

end LeanCanny.Algebra.IntegralMixedPscUpperBits
