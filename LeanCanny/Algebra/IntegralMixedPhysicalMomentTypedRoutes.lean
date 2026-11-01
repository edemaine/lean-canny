/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalMomentRoutes
/-! # The three typed augmented blocks use actual phase-nineteen entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] characteristic characteristicAccess

noncomputable abbrev momentAccess (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F) :=
  IntegralCriticalFlatMomentBits.access P a (characteristic P F) (characteristicAccess P a F h)

theorem rowTask_value (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (c : List Bool)
    (i : Fin ((moment P F).dimension c)) (r t : Fin ((moment P F).rank c)) :
    IntegralMixedPhysicalMatrixBits.actionEntry P F (IntegralCriticalFlatMomentTasks.rowTask P (characteristic P F)
      (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val))) =
      (momentAccess P a F h).row (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val)) := by
  let s := stage (characteristic P F) (IntegralCriticalFlatMomentBits.packet P c)
  let parent := original (IntegralCriticalFlatMomentBits.packet P c)
  have HI : i.val < (characteristic P F).dimension parent - s - 1 := i.isLt
  let u : Fin ((characteristic P F).dimension parent) := ⟨s, by omega⟩
  let v : Fin ((characteristic P F).dimension parent) := ⟨s + 1 + i.val, by omega⟩
  change IntegralMixedPhysicalMatrixBits.actionEntry P F (IntegralCriticalFlatBerkowitzQuery.entryWriter P (characteristic P F)
    (rowQuery (characteristic P F) (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P)
      (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val))))) = _
  rw [IntegralBlockMomentBits.requery_context, rowQuery_packet ]
  rw [(momentAccess P a F h).row_eq]
  exact actionChild_value P F g parent u v r t

theorem columnTask_value (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (c : List Bool)
    (i : Fin ((moment P F).dimension c)) (r t : Fin ((moment P F).rank c)) :
    IntegralMixedPhysicalMatrixBits.actionEntry P F (IntegralCriticalFlatMomentTasks.columnTask P (characteristic P F)
      (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val))) =
      (momentAccess P a F h).column (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val)) := by
  let s := stage (characteristic P F) (IntegralCriticalFlatMomentBits.packet P c)
  let parent := original (IntegralCriticalFlatMomentBits.packet P c)
  have HI : i.val < (characteristic P F).dimension parent - s - 1 := i.isLt
  let u : Fin ((characteristic P F).dimension parent) := ⟨s, by omega⟩
  let v : Fin ((characteristic P F).dimension parent) := ⟨s + 1 + i.val, by omega⟩
  change IntegralMixedPhysicalMatrixBits.actionEntry P F (IntegralCriticalFlatBerkowitzQuery.entryWriter P (characteristic P F)
    (columnQuery (characteristic P F) (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P)
      (pair (IntegralBlockMomentBits.context c r.val t.val) (BinaryNatCode.encode i.val))))) = _
  rw [IntegralBlockMomentBits.requery_context, columnQuery_packet ]
  rw [(momentAccess P a F h).column_eq]
  exact actionChild_value P F g parent v u r t

theorem matrixTask_value (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedPhysicalQueryBits.InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (c : List Bool)
    (i j : Fin ((moment P F).dimension c)) (r t : Fin ((moment P F).rank c)) :
    IntegralMixedPhysicalMatrixBits.actionEntry P F (IntegralCriticalFlatMomentTasks.matrixTask P (characteristic P F)
      (pair (IntegralBlockMomentBits.context c r.val t.val)
        (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      (momentAccess P a F h).entry (pair (IntegralBlockMomentBits.context c r.val t.val)
        (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) := by
  let s := stage (characteristic P F) (IntegralCriticalFlatMomentBits.packet P c)
  let parent := original (IntegralCriticalFlatMomentBits.packet P c)
  have HI : i.val < (characteristic P F).dimension parent - s - 1 := i.isLt
  have HJ : j.val < (characteristic P F).dimension parent - s - 1 := j.isLt
  let u : Fin ((characteristic P F).dimension parent) := ⟨s + 1 + i.val, by omega⟩
  let v : Fin ((characteristic P F).dimension parent) := ⟨s + 1 + j.val, by omega⟩
  change IntegralMixedPhysicalMatrixBits.actionEntry P F (IntegralCriticalFlatBerkowitzQuery.entryWriter P (characteristic P F)
    (matrixQuery (characteristic P F) (IntegralBlockPowerBits.requeryEntry (IntegralCriticalFlatMomentBits.packet P)
      (pair (IntegralBlockMomentBits.context c r.val t.val)
        (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))))) = _
  rw [IntegralBlockMomentBits.requery_context, matrixQuery_packet ]
  rw [(momentAccess P a F h).entry_eq]
  exact actionChild_value P F g parent u v r t

end LeanCanny.Algebra.IntegralMixedPhysicalUpperBits
